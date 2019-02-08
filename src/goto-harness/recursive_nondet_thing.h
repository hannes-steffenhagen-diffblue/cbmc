#include <map>

#include <util/expr.h>
#include <util/symbol_table.h>
#include <util/std_types.h>

struct nondet_thing_optionst
{
  
};

class recursive_nondet_thing
{
public:
  recursive_nondet_thing(nondet_thing_optionst options, symbol_tablet &symtab)
    : options(options), symtab(symtab) {}

  exprt get_initialiser(const typet &, const exprt &depth);

private:
  nondet_thing_optionst options;
  symbol_tablet &symtab;
  std::map<typet, irep_idt> constructor_for_type;

  irep_idt make_constructor_for_type(const typet &);
  irep_idt make_nondet_constructor_for_type(const typet &);
};