#include "recursive_nondet_thing.h"

#include <goto-programs/goto_convert_functions.h>
#include <util/allocate_objects.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/pointer_offset_size.h>

// TODO: REMOVE DEBUG STUFF

#include <iostream>

void recursive_nondet_thing::get_initialiser(const exprt &lhs, std::size_t depth, code_blockt &body)
{
  auto const &type = lhs.type();
  if(type.id() == ID_struct_tag)
  {
    get_struct_tag_initializer(lhs, depth, body);
  } else if(type.id() == ID_pointer) {
    get_pointer_initializer(lhs, depth, body);
  } else {
    get_nondet_initializer(lhs, depth, body);
  }
}


symbol_exprt recursive_nondet_thing::get_malloc_function() {
  std::clog << "getting malloc function" << std::endl;
  auto malloc_sym = goto_model.symbol_table.lookup("malloc");
  if(malloc_sym == nullptr) {
    std::clog << "malloc not found in symbol table, adding..." << std::endl;
    symbolt new_malloc_sym;
    new_malloc_sym.type = code_typet{
      code_typet{{code_typet::parametert{size_type()}},
                 pointer_type(empty_typet{})}
    };
    new_malloc_sym.name = new_malloc_sym.pretty_name = new_malloc_sym.base_name
      = "malloc";
    new_malloc_sym.mode = ID_C;
    goto_model.symbol_table.insert(new_malloc_sym);
    // goto_model.goto_functions.function_map["malloc"].type =
    //   to_code_type(new_malloc_sym.type);
    return new_malloc_sym.symbol_expr();
  }
  return malloc_sym->symbol_expr();
}


void recursive_nondet_thing::get_struct_tag_initializer(const exprt &lhs, std::size_t depth, code_blockt& body)
{
  PRECONDITION(lhs.type().id() == ID_struct_tag);
  auto const &type = to_struct_tag_type(lhs.type());
  auto const &ns = namespacet{goto_model.symbol_table};
  for(auto const &component : ns.follow_tag(type).components())
  {
    get_initialiser(member_exprt{lhs, component}, depth, body);
  }
}

void recursive_nondet_thing::get_pointer_initializer(const exprt &lhs, std::size_t depth, code_blockt &body)
{
  PRECONDITION(lhs.type().id() == ID_pointer);
  auto const &type = to_pointer_type(lhs.type());
  allocate_objectst allocate_objects{ID_C, type.source_location(), "initializer", goto_model.symbol_table};
  exprt choice;
  if(depth > options.min_null_tree_depth && depth < options.max_nondet_tree_depth)
  {
    choice = allocate_objects.allocate_automatic_local_object(bool_typet{}, "choice");
  }
  auto pointee = allocate_objects.allocate_automatic_local_object(type.subtype(), "pointee");
  allocate_objects.declare_created_symbols(body);
  body.add(code_assignt{lhs, null_pointer_exprt{type}});
  auto const &ns = namespacet{goto_model.symbol_table};
  if(depth < options.min_null_tree_depth && depth < options.max_nondet_tree_depth) {
    get_initialiser(pointee, depth + 1, body);
    body.add(code_assignt{lhs, address_of_exprt{pointee}});
  } else if(depth < options.max_nondet_tree_depth) {
    code_blockt then_case{};
    get_initialiser(pointee, depth + 1, then_case);
    then_case.add(code_assignt{lhs, address_of_exprt{pointee}});
    body.add(code_ifthenelset{choice, then_case});
  }
}

void recursive_nondet_thing::get_nondet_initializer(const exprt& lhs, std::size_t depth, code_blockt &body)
{
  body.add(code_assignt{lhs, side_effect_expr_nondett{lhs.type()}});
}