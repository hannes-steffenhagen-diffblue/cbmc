/******************************************************************\

Module: goto_harness_parse_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H
#define CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/message.h>
#include <util/ui_message.h>

#define GOTO_HARNESS_OPTIONS \
  "(version)" \
  // end GOTO_HARNESS_OPTIONS

class goto_harness_parse_optionst
  : public parse_options_baset
  , public messaget
{
public:
  int doit() override;
  void help() override;

  goto_harness_parse_optionst(int argc, const char *argv[]);
  goto_harness_parse_optionst(const goto_harness_parse_optionst&) = delete;
  goto_harness_parse_optionst(goto_harness_parse_optionst&&);
private:
  ui_message_handlert ui_message_handler;
};

#endif // CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H
