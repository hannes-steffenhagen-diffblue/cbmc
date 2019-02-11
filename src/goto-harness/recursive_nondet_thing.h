#include <map>

#include <util/expr.h>
#include <goto-programs/goto_model.h>
#include <util/message.h>
#include <util/std_types.h>

struct nondet_thing_optionst
{
  std::size_t min_null_tree_depth = 1;
  std::size_t max_nondet_tree_depth = 2;
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

  exprt get_initialiser(const typet &, std::size_t depth, code_blockt &body);

private:
  const nondet_thing_optionst options;
  goto_modelt &goto_model;
  message_handlert &message_handler;
  symbol_exprt get_malloc_function();

  exprt get_struct_tag_initializer(const struct_tag_typet& type, std::size_t depth, code_blockt& body);
  exprt get_pointer_initializer( const pointer_typet &type, std::size_t depth, code_blockt &body);
  exprt get_nondet_initializer(const typet& type, std::size_t depth, code_blockt &body);
};
