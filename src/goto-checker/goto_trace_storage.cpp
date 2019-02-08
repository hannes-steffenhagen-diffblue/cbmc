/*******************************************************************\

Module: Goto Trace Storage

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Trace Storage

#include "goto_trace_storage.h"
#include <iostream>

goto_trace_storaget::goto_trace_storaget(const namespacet &ns) : ns(ns)
{
}

const goto_tracet &goto_trace_storaget::insert(goto_tracet &&trace)
{
  traces.push_back(std::move(trace));
  const auto &last_step = traces.back().get_last_step();
  DATA_INVARIANT(
    last_step.is_assert(), "last goto trace step expected to be assertion");
  std::clog << "[TRACE] Emplacing: " << last_step.property_id << std::endl;
  property_id_to_trace_index.emplace(last_step.property_id, traces.size() - 1);
  return traces.back();
}

const goto_tracet &goto_trace_storaget::insert_all(goto_tracet &&trace)
{
  traces.push_back(std::move(trace));
  const auto &all_property_ids = traces.back().get_all_property_ids();
  DATA_INVARIANT(
    !all_property_ids.empty(), "a trace must violate at least one assertion");
  for(const auto &property_id : all_property_ids)
  {
    std::clog << "[TRACE] Emplacing: " << property_id << std::endl;
    property_id_to_trace_index.emplace(property_id, traces.size() - 1);
  }
  return traces.back();
}

const std::vector<goto_tracet> &goto_trace_storaget::all() const
{
  return traces;
}

const goto_tracet &goto_trace_storaget::
operator[](const irep_idt &property_id) const
{
  std::clog << "[TRACE] property_id_to_trace_index.size()"
            << property_id_to_trace_index.size() << std::endl;
  for(auto const &pi_ti : property_id_to_trace_index)
  {
    std::clog << "[TRACE] Has id" << pi_ti.first << std::endl;
  }
  const auto trace_found = property_id_to_trace_index.find(property_id);
  PRECONDITION(trace_found != property_id_to_trace_index.end());

  return traces.at(trace_found->second);
}

const namespacet &goto_trace_storaget::get_namespace() const
{
  return ns;
}
