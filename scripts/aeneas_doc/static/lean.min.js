/*! `lean` grammar compiled for Highlight.js 11.9.0 */
(()=>{var e=(()=>{"use strict";function e(e){
return e&&e.__esModule&&Object.prototype.hasOwnProperty.call(e,"default")?e.default:e
}return e((e=>{var a={$pattern:/\w+|\u03bb|\u2200|\u03a0|\u2203|:=?/u,
keyword:"theorem|10 lemma|10 definition def class structure instance example inductive coinductive axiom axioms hypothesis constant constants universe universes variable variables parameter parameters begin end infix infixr import open theory prelude renaming hiding exposing calc  match do  by let in extends fun assume #check #eval #reduce #print \u03bb \u2200 \u2203 \u2a01 \u03a0",
built_in:"Type Prop|10 Sort rw|10 rewrite rwa erw subst substs simp dsimp simpa simp_intros finish unfold unfold1 dunfold unfold_projs unfold_coes delta cc ac_reflexivity ac_refl existsi|10 cases rcases with intro intros introv by_cases refl rfl funext propext exact exacts refine apply eapply fapply apply_with apply_instance induction rename assumption revert generalize specialize clear contradiction by_contradiction by_contra trivial exfalso symmetry transitivity destruct constructor econstructor left right split injection injections repeat try continue skip swap solve1 abstract all_goals any_goals done fail_if_success success_if_fail guard_target guard_hyp have replace at suffices show from congr congr_n congr_arg norm_num ring ",
literal:"tt ff",meta:"noncomputable|10 private protected meta mutual",
section:"section namespace end",sorry:"sorry admit",symbol:":="
},n=e.COMMENT("--","$"),s=e.COMMENT("/-[^-]","-/"),t={className:"theorem",
beginKeywords:"def theorem lemma class instance structure",end:/:=/,
excludeEnd:!0,contains:[{className:"keyword",begin:/extends/,contains:[{
className:"symbol",begin:/:=/,endsParent:!0}]},e.inherit(e.TITLE_MODE,{
begin:/[A-Za-z_][\w\u207F-\u209C\u1D62-\u1D6A\u2079\']*/}),{className:"params",
begin:/[([{]/,end:/[)\]}]/,endsParent:!1,keywords:a},{className:"symbol",
begin:/:=/,endsParent:!0},{className:"symbol",begin:/:/,endsParent:!0}],
keywords:a};return{name:"lean",keywords:a,
contains:[e.QUOTE_STRING_MODE,e.NUMBER_MODE,n,s,{className:"doctag",
begin:"/-[-!]",end:"-/"},t,{className:"meta",begin:"@\\[",end:"\\]"},{
className:"meta",begin:"^attribute",end:"$"},{begin:/\u27e8/}]}}))})()
;hljs.registerLanguage("lean",e)})();