#include <map>

#include <util/expr.h>
#include <goto-programs/goto_model.h>
#include <util/message.h>
#include <util/std_types.h>

struct nondet_thing_optionst
{
  std::size_t min_null_tree_depth = 2;
  std::size_t max_nondet_tree_depth = 3;
};

class recursive_nondet_thing
{
public:
  recursive_nondet_thing(
    nondet_thing_optionst options,
    goto_modelt &goto_model,
    message_handlert &message_handler)
    : options(options), goto_model(goto_model), message_handler(message_handler)
  {
  }

  exprt get_initialiser(const typet &, const exprt &depth);

private:
  const nondet_thing_optionst options;
  goto_modelt &goto_model;
  message_handlert &message_handler;
  std::map<typet, irep_idt> constructor_for_type;

  irep_idt make_constructor_for_type(const typet &);
  irep_idt make_struct_constructor(const struct_tag_typet &);
  irep_idt make_nondet_constructor_for_type(const typet &);
  symbolt &register_constructor_for_type(const typet &);
  void finalize_constructor(const symbolt &constructor_symbol);

  irep_idt make_pointer_constructor(const pointer_typet &type);
  symbol_exprt get_depth_param_from_constructor(const symbolt &constructor);
  symbol_exprt get_malloc_function();
};
