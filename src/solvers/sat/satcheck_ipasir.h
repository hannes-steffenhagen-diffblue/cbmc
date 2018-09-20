/*******************************************************************\

Module:

Author: Norbert Manthey, nmanthey@amazon.com

See \ref compilation-and-development-subsection-sat-solver for build
instructions.

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H
#define CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H

#include "cnf.h"

/// Interface for generic SAT solver interface IPASIR
class satcheck_ipasirt:public cnf_solvert
{
public:
  satcheck_ipasirt();
  virtual ~satcheck_ipasirt() override;

  /// This method returns the description produced by the linked SAT solver
  virtual const std::string solver_text() override;

  virtual resultt prop_solve() override;

  /// This method returns the truth value for a literal of the current SAT model
  virtual tvt l_get(literalt a) const override final;

  virtual void lcnf(const bvt &bv) override final;

  /* This method is not supported, and currently not called anywhere in CBMC */
  virtual void set_assignment(literalt a, bool value) override;

  virtual void set_assumptions(const bvt &_assumptions) override;

  virtual bool is_in_conflict(literalt a) const override;
  virtual bool has_set_assumptions() const override final { return true; }
  virtual bool has_is_in_conflict() const override final { return true; }

protected:
  void *solver;

  bvt assumptions;
};

#endif // CPROVER_SOLVERS_SAT_SATCHECK_IPASIR_H
