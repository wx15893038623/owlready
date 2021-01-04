class ObjectPropertyClass(ReasoningPropertyClass):
  _owl_type = owl_object_property
  
  def __init__(Prop, name, bases, obj_dict):
    super().__init__(name, bases, obj_dict)
    
    if SymmetricProperty in Prop.is_a:
      type.__setattr__(Prop, "_inverse_storid", Prop.storid)
      Prop._inverse_property = Prop
    else:
      Prop._define_inverse_property()

  def _define_inverse_property(Prop):
    for inverse_storid in Prop.namespace.world._get_obj_triples_sp_o(Prop.storid, owl_inverse_property):
      if inverse_storid > 0: break
    else:
      for inverse_storid in Prop.namespace.world._get_obj_triples_po_s(owl_inverse_property, Prop.storid):
        if inverse_storid > 0: break
      else: inverse_storid = 0
    type.__setattr__(Prop, "_inverse_storid", inverse_storid or 0)
    if inverse_storid: type.__setattr__(Prop, "_inverse_property", Prop.namespace.world._get_by_storid(inverse_storid))
    else:              type.__setattr__(Prop, "_inverse_property", None)
    
  def get_inverse_property(Prop):
    return Prop._inverse_property
  
  def set_inverse_property(Prop, value):
    if value:
      Prop.namespace.ontology._set_obj_triple_spo(Prop.storid, owl_inverse_property, value and value.storid)
      type.__setattr__(Prop, "_inverse_property", value)
      type.__setattr__(Prop, "_inverse_storid", value.storid)
      if not value._inverse_property is Prop: value.inverse_property = Prop
    else:
      inverse = Prop._inverse_property
      type.__setattr__(Prop, "_inverse_property", value)
      Prop.namespace.ontology._del_obj_triple_spo(Prop.storid, owl_inverse_property, None)
      type.__setattr__(Prop, "_inverse_storid", 0)
      if inverse._inverse_property: inverse.inverse_property = None
      
  inverse_property = inverse = property(get_inverse_property, set_inverse_property)
  
  def _class_is_a_changed(Prop, old):
    super()._class_is_a_changed(old)
    if   (SymmetricProperty in old) and (not SymmetricProperty in Prop.is_a):
      if Prop._inverse_property: type.__setattr__(Prop, "_inverse_storid", Prop._inverse_property.storid)
      else:                      type.__setattr__(Prop, "_inverse_storid", 0)
    elif (SymmetricProperty in Prop.is_a) and (not SymmetricProperty in old):
      type.__setattr__(Prop, "_inverse_storid", Prop.storid)
      
      
  def _get_value_for_individual(Prop, entity):
    value = (entity.namespace.world._get_obj_triple_sp_o(entity.storid, Prop.storid)
         or (Prop._inverse_storid and
             entity.namespace.world._get_obj_triple_po_s(Prop._inverse_storid, entity.storid)) )
    if value:
      return entity.namespace.ontology._to_python(value)
    
  def _get_inverse_value_for_individual(Prop, entity):
    value = (entity.namespace.world._get_obj_triple_po_s(Prop.storid, entity.storid)
         or (Prop._inverse_storid and
             entity.namespace.world._get_obj_triple_sp_o(entity.storid, Prop._inverse_storid)) )
    if value:
      return entity.namespace.ontology._to_python(value)
    
  def _get_value_for_class(Prop, entity):
    if   Prop._class_property_relation: return Prop._get_value_for_individual(entity)
    
    elif Prop._class_property_some:
      for r in _property_value_restrictions(entity, Prop):
        if (r.type == VALUE) or (r.type == SOME) or ((r.type == EXACTLY) and r.cardinality >= 1) or ((r.type == MIN) and r.cardinality >= 1): return r.value
        
    elif Prop._class_property_only:
      for r in _property_value_restrictions(Class, Prop):
        if (r.type == ONLY):
          for value in _flatten_only(r): return value
          
          
  def _get_values_for_individual(Prop, entity):
    if Prop._inverse_storid:
      return IndividualValueList((entity.namespace.ontology._to_python(o)
                                  for o in entity.namespace.world._get_obj_triples_spi_o(entity.storid, Prop.storid, Prop._inverse_storid)),
                                  entity, Prop)
    else:
      return IndividualValueList((entity.namespace.ontology._to_python(o)
                                  for o in entity.namespace.world._get_obj_triples_sp_o(entity.storid, Prop.storid)),
                                  entity, Prop)
    
  def _get_inverse_values_for_individual(Prop, entity):
    if Prop._inverse_storid:
      return InverseIndividualValueList((entity.namespace.ontology._to_python(s)
                                         for s in entity.namespace.world._get_obj_triples_pio_s(Prop.storid, Prop._inverse_storid, entity.storid)),
                                         entity, Prop)
    else:
      return InverseIndividualValueList((entity.namespace.ontology._to_python(s)
                                         for s in entity.namespace.world._get_obj_triples_po_s(Prop.storid, entity.storid)),
                                         entity, Prop)
    
  def _get_values_for_class(Prop, entity):
    if   Prop._class_property_relation: return Prop._get_values_for_individual(entity)
    
    elif Prop._class_property_some:
      return ClassValueList(set(r.value for r in _property_value_restrictions(entity, Prop)
                                if (r.type == VALUE) or (r.type == SOME) or ((r.type == EXACTLY) and r.cardinality >= 1) or ((r.type == MIN) and r.cardinality >= 1)),
                                entity, Prop)
    
    elif Prop._class_property_only:
      return ClassValueList(set(x for r in _property_value_restrictions(entity, Prop)
                                if (r.type == ONLY)
                                for x in _flatten_only(r) ), entity, Prop)
      
                                 
  def _get_indirect_values_for_individual(Prop, entity):
    world   = entity.namespace.world
    onto    = entity.namespace.ontology
    Props   = Prop.descendants()
    eqs     = list(entity.equivalent_to.self_and_indirect_equivalent())
    already_applied_class = set()
    
    prop_storids = []
    values       = set()
    if issubclass_python(Prop, ReflexiveProperty): values.add(entity)
    
    for P in Props:
      if issubclass(P, TransitiveProperty):
        if P._inverse_storid: prop_storids.append((P.storid, P._inverse_storid))
        else:                 prop_storids.append((P.storid, None))
      else:
        if P._inverse_storid:
          values.update(onto._to_python(o)
                        for eq in eqs
                        for g in (world._get_obj_triples_sp_o(eq.storid, P.storid), world._get_obj_triples_po_s(P._inverse_storid, eq.storid))
                        for o in g )
        else:
          values.update(onto._to_python(o)
                        for eq in eqs
                        for o in  world._get_obj_triples_sp_o(eq.storid, P.storid) )
          
    if prop_storids:
      for eq in eqs:
        new_values = [onto._to_python(o) for o in world._get_obj_triples_transitive_sp_indirect(eq.storid, prop_storids)]
        
        for o in new_values:
          values.add(o)
          if not o.__class__ in already_applied_class:
            values.update(Prop._get_indirect_values_for_class(o.__class__, True))
            already_applied_class.add(o.__class__)
          for o2 in o.equivalent_to.indirect():
            if not ((o2 in new_values) or (o2 in values)):
              values.add(o2)
              if not o2.__class__ in already_applied_class:
                values.update(Prop._get_indirect_values_for_class(o2.__class__, True))
                already_applied_class.add(o2.__class__)
                
    for eq in eqs:
      if not eq.__class__ in already_applied_class:
        values.update(Prop._get_indirect_values_for_class(eq.__class__, True))
        already_applied_class.add(eq.__class__)
        
    return list(values)
                        
  # def _get_indirect_inverse_values_for_individual(Prop, entity):
  #   world   = entity.namespace.world
  #   onto    = entity.namespace.ontology
  #   Props   = Prop.descendants()
  #   eqs     = list(entity.equivalent_to.self_and_indirect_equivalent())
  #   already_applied_class = set()
    
  #   prop_storids = []
  #   values       = set()
  #   for P in Props:
  #     if issubclass(P, TransitiveProperty):
  #       if P._inverse_storid: prop_storids.append((P.storid, P._inverse_storid))
  #       else:                 prop_storids.append((P.storid, None))
  #     else:
  #       if P._inverse_storid:
  #         values.update(onto._to_python(o)
  #                       for eq in eqs
  #                       for g in (world._get_obj_triples_sp_o(eq.storid, P.storid), world._get_obj_triples_po_s(P._inverse_storid, eq.storid))
  #                       for o in g )
  #       else:
  #         values.update(onto._to_python(o)
  #                       for eq in eqs
  #                       for o in  world._get_obj_triples_sp_o(eq.storid, P.storid) )
          
  #   if prop_storids:
  #     for eq in eqs:
  #       new_values = [onto._to_python(s) for s in world._get_obj_triples_transitive_po_indirect(eq.storid, prop_storids)]
        
  #       for o in new_values:
  #         values.add(o)
  #         if not o.__class__ in already_applied_class:
  #           values.update(Prop._get_indirect_values_for_class(o.__class__, True))
  #           already_applied_class.add(o.__class__)
  #         for o2 in o.equivalent_to.indirect():
  #           if not ((o2 in new_values) or (o2 in values)):
  #             values.add(o2)
  #             if not o2.__class__ in already_applied_class:
  #               values.update(Prop._get_indirect_values_for_class(o2.__class__, True))
  #               already_applied_class.add(o2.__class__)
                
  #   for eq in eqs:
  #     if not eq.__class__ in already_applied_class:
  #       values.update(Prop._get_indirect_values_for_class(eq.__class__, True))
  #       already_applied_class.add(eq.__class__)
        
  #   return list(values)
  
  def _get_indirect_values_for_class(Prop, entity, transitive_exclude_self = True):
    world = entity.namespace.world
    onto  = entity.namespace.ontology
    Props = Prop.descendants()
    
    if   Prop._class_property_relation:
      storids = [ancestor.storid for ancestor in entity.ancestors()]
      
      prop_storids = []
      values       = set()
      for P in Props:
        if issubclass_python(P, TransitiveProperty):
          if P._inverse_storid: prop_storids.append((P.storid, P._inverse_storid))
          else:                 prop_storids.append((P.storid, None))
        else:
          if P._inverse_storid:
            values.update(onto._to_python(o) for storid in storids
                                             for g in (world._get_obj_triples_sp_o(storid, P.storid),
                                                       world._get_obj_triples_po_s(P._inverse_storid, storid))
                                             for o in g )
          else:
            values.update(onto._to_python(o) for storid in storids
                                             for o in  world._get_obj_triples_sp_o(storid, P.storid) )
              
      if prop_storids:
        values.update(onto._to_python(o) for storid in storids
                                         for o in world._get_obj_triples_transitive_sp_indirect(storid, prop_storids))
        if transitive_exclude_self: values.discard(entity)


    elif Prop._class_property_some:
      if issubclass_python(Prop, TransitiveProperty):
        values = set()
        def walk(o):
          values.add(o)
          for r in _inherited_properties_value_restrictions(o, Props, set()):
            if   r.type == VALUE:
              if not r.value in values:
                for o2 in r.value.equivalent_to.self_and_indirect_equivalent():
                  if not o2 in values:
                    values.add(o2)
                    values.update(Prop._get_indirect_values_for_individual(o2))
                    
            elif (r.type == SOME) or ((r.type == EXACTLY) and r.cardinality >= 1) or ((r.type == MIN) and r.cardinality >= 1):
              if not r.value in values: walk(r.value)

          if isinstance(o, ThingClass):
            for e in o.equivalent_to.indirect():
              if not e in values: walk(e)
              
        walk(entity)
        if transitive_exclude_self: values.discard(entity)
        
      else:
        values = set(r.value for r in _inherited_properties_value_restrictions(entity, Props, set())
                             if (r.type == VALUE) or (r.type == SOME) or ((r.type == EXACTLY) and r.cardinality >= 1) or ((r.type == MIN) and r.cardinality >= 1) )
        
    elif Prop._class_property_only: # Effect of transitivity on ONLY restrictions is unclear -- probably no effect?
      or_valuess = [set(_flatten_only(r)) for r in _inherited_properties_value_restrictions(entity, Props, set())
                                          if (r.type == ONLY)]
      values = or_valuess[0]
      for or_values in or_valuess[1:]:
        new_values = values & or_values
        for vs1, vs2 in ((values, or_values), (or_values, values)):
          vs2_classes = tuple(o for o in vs2 if isinstance(o, EntityClass))
          for v in vs1 - vs2:
            if isinstance(v, EntityClass):
              if issubclass(v, vs2_classes): new_values.add(v)
            else:
              if isinstance(v, vs2_classes): new_values.add(v)
        values = new_values
        
    return list(values)
  
  def _set_value_for_individual(Prop, entity, value):
    if value is None: entity.namespace.ontology._del_obj_triple_spo(entity.storid, Prop.storid, None)
    else:             entity.namespace.ontology._set_obj_triple_spo(entity.storid, Prop.storid, value.storid)
    if (not instance(entity, EntityClass)) and (Prop is entity.namespace.world._props.get(Prop._python_name)):
      entity.__dict__[Prop.python_name] = value
      
  def _set_value_for_class (Prop, entity, value ): Prop._get_values_for_class(entity).reinit([value])