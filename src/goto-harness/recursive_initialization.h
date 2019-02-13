/******************************************************************\

Module: recursive_initialization

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H
#define CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H

#include <map>

#include <goto-programs/goto_model.h>
#include <util/expr.h>
#include <util/message.h>
#include <util/std_types.h>

struct recursive_initialization_configt
{
  std::size_t min_null_tree_depth = 1;
  std::size_t max_nondet_tree_depth = 2;
};

class recursive_initializationt
{
public:
  recursive_initializationt(
    recursive_initialization_configt initialization_config,
    goto_modelt &goto_model,
    message_handlert &message_handler);

  void initialize(const exprt &lhs, std::size_t depth, code_blockt &body);

private:
  const recursive_initialization_configt initialization_config;
  goto_modelt &goto_model;
  message_handlert &message_handler;
  symbol_exprt get_malloc_function();

  void get_struct_tag_initializer(
    const exprt &lhs,
    std::size_t depth,
    code_blockt &body);
  void get_pointer_initializer(
    const exprt &lhs,
    std::size_t depth,
    code_blockt &body);
  void get_nondet_initializer(
    const exprt &lhs,
    std::size_t depth,
    code_blockt &body);
};

#endif // CPROVER_GOTO_HARNESS_RECURSIVE_INITIALIZATION_H
