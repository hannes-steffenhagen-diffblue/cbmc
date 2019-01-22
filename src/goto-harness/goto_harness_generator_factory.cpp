/******************************************************************\

Module: goto_harness_generator_factory

Author: Diffblue Ltd.

\******************************************************************/

#include "goto_harness_generator_factory.h"
#include "default_goto_harness_generator.h"

#include <util/string_utils.h>
#include <util/make_unique.h>
#include <util/exception_utils.h>

#include <functional>
#include <algorithm>
#include <iterator>
#include <sstream>

struct erase_goto_harness_factoryt
{
  const irep_idt name;
  using build_t = std::function<std::unique_ptr<goto_harness_generatort>()>;
  const build_t build;

  erase_goto_harness_factoryt(const irep_idt &name, build_t build)
    : name{name}, build{build}
  {}

  template<typename Generator>
  static erase_goto_harness_factoryt erase()
  {
    return erase_goto_harness_factoryt{
      irep_idt{Generator::name},
        [](){return std::unique_ptr<goto_harness_generatort>{util_make_unique<Generator>()};} };
  }
};

std::unique_ptr<goto_harness_generatort> goto_harness_generator_factory(const irep_idt &generator_name) {
  auto const generators = std::vector<erase_goto_harness_factoryt>{
    erase_goto_harness_factoryt::erase<default_goto_harness_generatort>()
  };
  for(auto const &generator : generators) {
    if(generator.name == generator_name) {
      return generator.build();
    }
  }

  // no generator with this name exists, error

  auto generator_names = std::vector<std::string>{};
  std::transform(generators.begin(), generators.end(),
                 std::back_inserter(generator_names),
                 [](const erase_goto_harness_factoryt& erased) { return id2string(erased.name); });
  auto join_strings_out = std::ostringstream{};
  throw invalid_command_line_argument_exceptiont(
    "no generator with name `" + id2string(generator_name) + "' exists",
      std::string{"--" GOTO_HARNESS_GENERATOR_TYPE_OPT},
      "use one of: " + join_strings(join_strings_out,
                   generator_names.begin(), generator_names.end(),
                               ", ").str());
}
