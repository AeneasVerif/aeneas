module
public import Aeneas.Tactic.Step.PrepareIntroIspec
public section

namespace Aeneas.Std.WP

#register_spec_info {
    spec_name := ``Std.WP.spec
    arity := 3
    program_index := 1
    post_index := 2
    mk_spec_mono := ``Std.WP.spec_mono
    mk_spec_mono_skip_args := 2
    mk_spec_bind := ``Std.WP.spec_bind
    mk_spec_bind_skip_args := 4
    prepare_intro_outputs := ``Aeneas.Step.prepareIntroOutputs
    to_mvcgen := none
    liftings := #[
      { from_statement := ``Std.WP.ispec
        conversion_thm := ``Std.WP.ispec_spec
        conversion_thm_inferred_args := 3 }
    ]
  }

#register_spec_info {
    spec_name := ``Std.WP.dspec
    arity := 3
    program_index := 1
    post_index := 2
    mk_spec_mono := ``Std.WP.dspec_mono
    mk_spec_mono_skip_args := 2
    mk_spec_bind := ``Std.WP.dspec_bind
    mk_spec_bind_skip_args := 4
    prepare_intro_outputs := ``Aeneas.Step.prepareIntroOutputs
    to_mvcgen := none
    liftings := #[
      { from_statement := ``Std.WP.spec
        conversion_thm := ``Std.WP.spec_dspec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``Std.WP.ispec
        conversion_thm := ``Std.WP.ispec_dspec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``Std.WP.dispec
        conversion_thm := ``Std.WP.dispec_dspec
        conversion_thm_inferred_args := 3 }
    ]
  }

#register_spec_info {
    spec_name := ``Std.WP.ispec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``Std.WP.ispec_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``Std.WP.ispec_bind
    mk_spec_bind_skip_args := 7
    prepare_intro_outputs := ``Aeneas.Step.prepareIntroIspec
    discharge_tactic := some `iframe
    to_mvcgen := none
    liftings := #[
      { from_statement := ``Std.WP.spec
        conversion_thm := ``Std.WP.spec_ispec
        conversion_thm_inferred_args := 3 }
    ]
  }

#register_spec_info {
    spec_name := ``Std.WP.dispec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``Std.WP.dispec_mono
    mk_spec_mono_skip_args := 4
    mk_spec_bind := ``Std.WP.dispec_bind
    mk_spec_bind_skip_args := 7
    prepare_intro_outputs := ``Aeneas.Step.prepareIntroIspec
    discharge_tactic := some `iframe
    to_mvcgen := none
    liftings := #[
      { from_statement := ``Std.WP.ispec
        conversion_thm := ``Std.WP.ispec_dispec
        conversion_thm_inferred_args := 4 },
      { from_statement := ``Std.WP.spec
        conversion_thm := ``Std.WP.spec_dispec
        conversion_thm_inferred_args := 3 },
      { from_statement := ``Std.WP.dspec
        conversion_thm := ``Std.WP.dspec_dispec
        conversion_thm_inferred_args := 3 }
    ]
  }

end Aeneas.Std.WP
