/*******************************************************************\

 Module: analyses variable-sensitivity intervals

 Author: Diffblue Ltd.

\*******************************************************************/

#include <ostream>

#include <util/invariant.h>
#include <util/std_expr.h>

#include "abstract_enviroment.h"

#include "interval_abstract_value.h"

static inline exprt look_through_casts(exprt e) {
  while(e.id() == ID_typecast) {
    e = e.op0();
  }
  return e;
}

static inline constant_interval_exprt make_interval_expr(exprt e) {
  e = look_through_casts(e);
  if(e.id() == ID_constant_interval) {
    return to_constant_interval_expr(e);
  } else if(e.id() == ID_constant) {
    return constant_interval_exprt(e, e);
  } else {
    // not directly representable, so just return TOP
    return constant_interval_exprt(e.type());
  }
}

interval_abstract_valuet::interval_abstract_valuet(typet t):
  abstract_valuet(t), interval(t)
{}

interval_abstract_valuet::interval_abstract_valuet(typet t, bool tp, bool bttm):
  abstract_valuet(t, tp, bttm), interval(t)
{}

interval_abstract_valuet::interval_abstract_valuet(
  const constant_interval_exprt e)
  : interval_abstract_valuet(e, 0)
{

}

exprt interval_abstract_valuet::to_constant() const
{
  return abstract_objectt::to_constant();

#if 0
  if(!is_top() && !is_bottom())
  {
    return this->interval;
  }
  else
  {
    return abstract_objectt::to_constant();
  }
#endif
}

abstract_object_pointert interval_abstract_valuet::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  std::size_t num_operands = expr.operands().size();
  PRECONDITION(operands.size() == num_operands);

  const typet &type = expr.type();

  if(num_operands == 0)
    return environment.abstract_object_factory(type, ns, true);

  if(expr.id() == ID_plus)
  {
    constant_exprt zero = constant_interval_exprt::zero(type);
    constant_interval_exprt interval(zero);
    INVARIANT(interval.is_zero(), "Starting interval must be zero");

    for(const auto &op : operands)
    {
      const auto iav
        = std::dynamic_pointer_cast<const interval_abstract_valuet>(op);
      INVARIANT(iav, "");

      const constant_interval_exprt &interval_next = iav->interval;
      interval = interval.plus(interval_next);
    }

    INVARIANT(interval.type() == type, "");

    return environment.abstract_object_factory(type, interval, ns);
  }
  else if(num_operands == 1)
  {
    const auto iav =
      std::dynamic_pointer_cast<const interval_abstract_valuet>(operands[0]);

    INVARIANT(iav, "");

    const constant_interval_exprt &interval = iav->interval;

    // The typecast case should probably be handled by constant_interval_exprt
    // directly as well
    if(expr.id() == ID_typecast)
    {
      const typecast_exprt &tce = to_typecast_expr(expr);

      exprt lower = interval.get_lower();
      lower.type() = tce.type();

      exprt upper = interval.get_upper();
      upper.type() = tce.type();

      const constant_interval_exprt new_interval(lower, upper, tce.type());
      return environment.abstract_object_factory(tce.type(), new_interval, ns);
    }
    else
    {
      const constant_interval_exprt &interval_result = interval.eval(expr.id());
      INVARIANT(interval_result.type() == type, "");
      return environment.abstract_object_factory(type, interval_result, ns);
    }
  }
  else if(num_operands == 2)
  {
    const auto iav0
      = std::dynamic_pointer_cast<const interval_abstract_valuet>(operands[0]);

    INVARIANT(iav0, "");

    const auto iav1
      = std::dynamic_pointer_cast<const interval_abstract_valuet>(operands[1]);

    INVARIANT(iav1, "");

    const constant_interval_exprt &interval0 = iav0->interval;
    const constant_interval_exprt &interval1 = iav1->interval;

    // constant_interval_exprt currently does not correctly handle the type of
    // relational operators (it assigns to it the type of the first operand
    // as opposed to ID_bool)
#if 0
      constant_interval_exprt interval
        = interval0.eval(expr.id(), interval1);

      interval.type() = type;

      return environment.abstract_object_factory(type, interval, ns);
#endif

#if 1
    if(expr.id() == ID_equal)
    {

      INVARIANT(type.id() == ID_bool, "");

      tvt tv = interval0.equal(interval1);

      constant_interval_exprt ie(type);
      const constant_interval_exprt &interval = ie.tv_to_interval(tv);
      return environment.abstract_object_factory(type, interval, ns);
#endif
    }
  }

  return environment.abstract_object_factory(type, ns, true);
}

void interval_abstract_valuet::output(
  std::ostream &out, const ai_baset &ai, const namespacet &ns) const
{
  if(!is_top() && !is_bottom())
  {
    std::string lower_string;
    std::string upper_string;

    if(interval.get_lower().id() == ID_min) {
      lower_string = "-INF";
    } else {
      INVARIANT(interval.get_lower().id() == ID_constant,
          "We only support constant limits");
      lower_string = id2string(to_constant_expr(interval.get_lower()).get_value());
    }

    if(interval.get_upper().id() == ID_max) {
      upper_string = "+INF";
    } else {
      INVARIANT(interval.get_lower().id() == ID_constant,
                "We only support constant limits");
      upper_string = id2string(to_constant_expr(interval.get_upper()).get_value());
    }

    out << "[" << lower_string << ", " << upper_string << "]";
  }
  else
  {
    abstract_objectt::output(out, ai, ns);
  }
}

abstract_object_pointert interval_abstract_valuet::merge(
  abstract_object_pointert other) const
{
  interval_abstract_value_pointert cast_other=
    std::dynamic_pointer_cast<const interval_abstract_valuet>(other);
  if(cast_other)
  {
    return merge_intervals(cast_other);
  }
  else
  {
    return abstract_valuet::merge(other);
  }
}

/// Merge another interval abstract object with this one
/// \param other The interval abstract object to merge with
/// \return This if the other interval is subsumed by this,
///          other if this is subsumed by other.
///          Otherwise, a new interval abstract object
///          with the smallest interval that subsumes both
///          this and other
abstract_object_pointert interval_abstract_valuet::merge_intervals(
  interval_abstract_value_pointert other) const
{
  if(is_bottom() || other->interval.contains(interval))
  {
    return other;
  }
  else if(other->is_bottom() || interval.contains(other->interval))
  {
    return shared_from_this();
  }
  else
  {
    return std::make_shared<interval_abstract_valuet>(
      constant_interval_exprt(
        constant_interval_exprt::get_min(
          interval.get_lower(), other->interval.get_lower()),
        constant_interval_exprt::get_max(
          interval.get_upper(), other->interval.get_upper())),
      std::max(merge_count, other->merge_count) + 1);
  }
}

interval_abstract_valuet::interval_abstract_valuet(const exprt e, const abstract_environmentt &environment,
                                                   const namespacet &ns)
  : interval_abstract_valuet(make_interval_expr(e))
{}

interval_abstract_valuet::interval_abstract_valuet(
  constant_interval_exprt e,
  int merge_count)
  : abstract_valuet(e.type(), e.is_top() || merge_count > 10, e.is_bottom()),
    interval(e),
    merge_count(merge_count)
{
}