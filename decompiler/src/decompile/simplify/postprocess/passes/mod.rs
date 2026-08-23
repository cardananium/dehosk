mod bool_constr_collapse;
mod cancel_force_delay;
mod cosmetic_delay;
mod expect_tag;
mod list_cons;

pub(crate) use bool_constr_collapse::bool_constr_collapse;
pub(crate) use cancel_force_delay::cancel_force_delay_vars;
pub(crate) use cosmetic_delay::strip_cosmetic_delays;
pub(crate) use expect_tag::convert_expect_tag_to_constr_when;
pub(crate) use list_cons::normalize_list_cons_literals;

#[cfg(test)]
use cancel_force_delay::{count_var_usages, strip_force_on_var};

#[cfg(test)]
mod tests;
