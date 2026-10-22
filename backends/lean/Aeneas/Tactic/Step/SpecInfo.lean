module
public import Aeneas.Tactic.Step.PrepareIntroOutputs
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
    to_mvcgen := .some ``Std.WP.spec_to_mvcgen
    liftings := #[]
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
    to_mvcgen := .some ``Std.WP.dspec_to_mvcgen
    liftings := #[
      { from_statement := ``Std.WP.spec
        conversion_thm := ``Std.WP.spec_dspec
        conversion_thm_inferred_args := 3 }
    ]
  }

end Aeneas.Std.WP
