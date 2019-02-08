#include "recursive_nondet_thing.h"

#include <util/cprover_prefix.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/std_types.h>

exprt recursive_nondet_thing::get_initialiser(
  const typet &type,
  const exprt &depth)
{
  const auto it = constructor_for_type.find(type);
  irep_idt constructor_name;

  if (it == constructor_for_type.end())
  {
    constructor_name = make_constructor_for_type(type);
  } else {
    constructor_name = it->second;
  }

  return side_effect_expr_function_callt{
      symtab.lookup_ref(constructor_name).symbol_expr(),
      {depth}
    };
}

irep_idt recursive_nondet_thing::make_constructor_for_type(
  const typet &type)
{
  return make_nondet_constructor_for_type(type);
}

irep_idt recursive_nondet_thing::make_nondet_constructor_for_type(
  const typet &type)
{
  auto parameter = code_typet::parametert{
    unsignedbv_typet{32}
  };

  auto &parameter_symbol = get_fresh_aux_symbol(
      unsignedbv_typet{32},
      CPROVER_PREFIX,
      "nondet_constructor_depth",
      type.source_location(),
      ID_C,
      symtab);
    
  parameter.set_identifier(parameter_symbol.name);
  parameter_symbol.is_parameter = true;
  parameter_symbol.is_lvalue = true;

  symbolt &aux = get_fresh_aux_symbol(
      code_typet{{
        parameter
      },
      type},
      // name_prefix
      CPROVER_PREFIX,
      // basename_prefix
      "nondet_constructor" + id2string(type.id()),
      type.source_location(),
      ID_C,
      symtab);

  aux.value = code_returnt{
    side_effect_expr_nondett{
      type
    }
  };

  constructor_for_type.insert({type, aux.name});

  return aux.name;
}