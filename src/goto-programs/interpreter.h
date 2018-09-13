/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_INTERPRETER_H
#define CPROVER_GOTO_PROGRAMS_INTERPRETER_H

#include <util/message.h>
#include <util/exception_utils.h>

#include <string>

#include "goto_model.h"

class interpreter_errort : public cprover_exceptiont
{
public:
  explicit interpreter_errort(std::string message);
  std::string what() const noexcept override;
private:
  std::string message;
};

void interpreter(
  const goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_INTERPRETER_H
