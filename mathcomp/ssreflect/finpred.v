(* (c) Copyright 2024 Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*   This module provides facilities for handling (boolean) predicates with   *)
(* finite support, i.e., for which an explicit list of the values for which   *)
(* the predicate holds can given. These facilities include an extensive and   *)
(* extensible infrastructure for inferring this support. We always assume     *)
(* the type T of values has Equality, but as noted some of the operations and *)
(* theory also need T to have Choice. We define                               *)
(*   {finpred T} == the type of predicates with finite support. This type     *)
(*                  coerces to {pred T}, and this coercion will unify with    *)
(*                  many predicates that have finite support, thereby         *)
(*                  inferring said support (see list below).                  *)

(*  --> Because of coercions and reverse coercions, an operation or lemma     *)
(* expects an F : {finpred T} can be applied to any A that either coerces to  *)
(* {finpred T}, or to a P : {pred T} for which an F : {finpred T} that        *)
(* coerces to P can be found by unification. We summarize all three cases by  *)
(* stating that the operation or lemma expects "an A that is a finpred".      *)
(* --> The instances and coercions we define ensure that when A is a finpred, *)
(* A : {pred T} and A : {finpred T} : {pred T} are always convertible.        *)
(*                                                                            *)
(*  Finpred.support A == the support A, where A is a finpred, i.e., a         *)
(*                 duplicate-free sequence of the values on which A holds.    *)
(* --> Note that Finpred.support is NOT extensional; in particular equivalent *)
(* and even convertible predicates  P, Q : {pred T} that are finpreds may     *)
(* have different supports -- these may be nontivial permutations of each     *)
(* other. For that reason Finpred.support should only be used to define       *)
(* operations that can be computed up to permutation.                         *)
(* --> The enum operation below the preferred alternative, available when     *)
(* when T is choiceType.                                                      *)
(*                                                                            *)
(*   card A, #|A| == the number of elements for which a finpred A holds,      *)
(*                 i.e., the size of its support.                             *)
(*       pred0b A <=> the finpred A is empty (always false).                  *)
(*    A \subset B <=> the finpred A is a subset of the (plain) predicate B    *)
(*    A \proper B <=> the finpred P is a proper subset of the finpred B.      *)
(* [disjoint A & B] <=> the finpred A is disjoint from the predicate B.       *)
(*         enum A == a standard enumeration of the support of A, when T is a  *)
(*                 choiceType; enum is both extensional and stable -          *)
(*                 enum A is a subsequence of enum B when A \subset B.        *)
(*         pick A == some standard x on which a finpred A holds, or None if   *)
(*                 A is empty; pick A is extensional but can only be used     *)
(*                 when T is a choiceType.                                    *)
(*     dinjectiveb f A <=> f restricted to the finpred A is injective.        *)
(*                                                                            *)
(*  Coq will infer a finpred for a predicate A based on the body Ax of A for  *)
(* a fresh variable x : T, i.e., a partial reduction of A x, so we have both  *)
(* A x = Ax and A = fun x => Ax. The class of predicate bodies that are       *)
(* recognized as finpred bodies for a given variable x is extensible, but     *)
(* comprises at least:                                                        *)
(*  + false       is the body of the empty finpred for any x.                 *)
(*  + (A : {pred T}) x where A coerces to a {finpred T}, in particular for    *)
(*                A : {finpred T}, A : seq T, and A : {set T}.                *)
(*  + any Ax      is a finpred body for x when T is a finType (see module     *)
(*                fintype), but this is used as a last resort so that finpred *)
(*                inference is as consistent as possible with the non-finType *)
(*                case.                                                       *)
(*  + x == a, a == x where a does not depend on x.                            *)
(*  + x <= n      where n does not depend on x.                               *)
(*  + A (f x)     when A y is a finpred body for y and f is a function with   *)
(*                a bounded preimage. The latter notion is also extensible    *)
(*                and inferred from the expression fx = f x for x; it         *)
(*                includes cancellable and partially cancellable functions,   *)
(*                such as instances of the subType projector val, partially   *)
(*                applied pair and existT constructors, most nat arithmetic   *)
(*                functions, as well as composition of functions with a       *)
(*                bounded preimages.                                          *)
(*  + Ax || Bx    where Ax and Bx are both finpred bodies for x.              *)
(*  + Ax (+) Bx   where Ax and Bx are both finpred bodies for x.              *)
(*  + Ax && Bx    where Ax is a finpred body for x (Bx is any expression).    *)
(*  + Ax && Bx    where Bx is a finpred body for x, and Ax is manifestly      *)
(*                unlikely to be a finpred body (unless T is a finType).      *)
(*                The latter notion is also extensible, but by default only   *)
(*                covers cases where Ax does not depend on x (note that the   *)
(*                Ax = false case is covered by the first rule), Ax is ~~ Cx, *)
(*                or Ax is m <= fx where m does not depend on x.              *)
(*  + A (f x) && B x where T is isomorphic to a sigma type {i : I & T_ i},    *)
(*                in which f x maps x to the first component (the i) of the   *)
(*                corresponding dependent pair, A i is a finpred body for i,  *)
(*                and for all i, B (g i y) is a finpred body for y : T_ i,    *)
(*                where g i y : T corresponds to the dependent pair           *)
(*                existT T_ i y.                                              *)
(* --> Caveat: currently the sigma-type case is only partially implemented.   *)
(*  The implementation only handles simple abstract cases such as the predX   *)
(*  combinator.                                                               *)
(*  + (if Cx then Ax else Bx) when both Ax and Bx are finpred bodies for x.   *)
(*  + (if Cx then Ax else Bx) when both Cx and Bx are finpred bodies for x,   *)
(*    and Ax is manifestly unlikely to be a finpred body (see the second case *)
(*    for Ax && Bx above).                                                    *)
(*                                                                            *)
(*    The finpred inference for a given A attempts to minimize duplication of *)
(* the contents of A. There is no duplication when A coerces to {finpred T}   *)
(* or A is the {pred T} coercion of a B that coerces to {finpred T}. In other *)
(* cases we first infer an F : {finpred T} whose coercion to {pred T} is      *)
(* convertible to but may differ considerably from A, then inject in it a     *)
(* copy of the original A to obtain a finpred that coerces exactly to A.      *)
(*    The initially inferred F follows the structure of A but does not        *)
(* duplicate any part of it (with one possible exception for the sigma type   *)
(* case for &&) so the final inferred finpred only contains two copies of A.  *)
(*    Note that reverse coercion, if used, will add a third copy for display  *)
(* purposes (or a second one in the coercion-to-pred-and-finpred case). This  *)
(* extra copy is actually unnecessary here as we ensure that the inferred     *)
(* finpred always diplays as A; perhaps a future version of Coq will provide  *)
(* some means to turn off the insertion of the reverse_coercion constant when *)
(* it is not needed.                                                          *)
(*   We define instances that infer finpreds both when the predicate body is  *)
(* well delimited as we unify A : {pred T} with ?F : {finpred T} coerced to   *)
(* {pred T}, e.g., when unifying (a \in A) with (?v \in ?F), as well as when  *)
(* the predicate body is undelimited and we have to unify Ax : bool with      *)
(* (?F : {pred T}) x for some variable x : T , e.g., when unifying  (a \in A) *)
(* with (?v \in [predU1 ?a1 & ?F]).                                           *)
(*   In the latter case we exploit the higher order (Miller pattern) feature  *)
(* of Coq unification to infer A = [pred x | Ax] from Ax and x, which we      *)
(* store in the inferred finpred F both for legibility and to allow           *)
(* rewrite inE to expand a \in F to Ax{a/x}. In either case we make sure that *)
(* F displays as A, and that simpl simplifies a \in F to just a \in c0 A      *)
(* where c0 is a fixed identity coercion function.                            *)
(* ---> One important Caveat: when using rewrite in the undelimited case,     *)
(* Coq will expand head constants in Ax before the attempting to grab the     *)
(* predicate body, leading to possible unwanted expansion in the inferred     *)
(* predicate, or even ruining the inference altogether, in particular when    *)
(* the head symbol is a computable eq_op (==) or a non-computable if.         *)

Module Export (coercions, canonicals) HOpattern.
Section HOpattern.
Unset Implicit Arguments.
Unset Printing Records.
Set Universe Polymorphism.
Universes s u.
Notation sType := (Type@{s}).
Notation uType := (Type@{u}).

Variable absT : uType. (* Type of abstracted term. *)

Variant packed : sType := Pack (U : uType) of U.

Variant unmatched : Set := BuildUnmatched.
Example Unmatchable : unmatched. Proof. split. Qed.
Definition frozen := unmatched -> uType.
Notation freeze fU := (fU Unmatchable).
Structure unfrozen : sType :=
  Unfrozen { _ : frozen; _ : uType; unfrozen_Type :> uType }.
Definition unfreeze (fU : frozen) (U : uType) := Unfrozen fU U (freeze fU).
Canonical InferFrozen (U : uType) := Unfrozen (fun=> U) U U.

Variant call : Set := Call.

Structure unify {U : sType} (u1 u2 : U) (next : call) : Set :=
  Unify { call_unify :> call }.
Canonical Unification (U : sType) u := @Unify U u u Call Call.

Variant hint : Set := Hint.

Definition PostTyped fail (U : uType) of U & call : hint := fail Unmatchable.
Definition FailHead of unmatched := Hint.
Notation PostTypeHint fail U u := (PostTyped fail U u Call).
Definition fixFail fail := unify FailHead fail Call.

Definition TryTypeArity of uType := Hint.
Definition TryForallArity (U : uType) of call := TryTypeArity U.
Definition TryNotSubtype (U : uType) of U := TryForallArity U.
Definition SuptypeHint (U : uType) (u : U) := TryNotSubtype U u Call.

Structure suptypePattern (S : uType) : sType :=
  SuptypePattern { suptype_hint :> hint}.
Canonical TypeArity@{i | i < u} :=
  SuptypePattern Type@{i} (TryTypeArity Type@{i}).
Canonical ForallArity (V0 V : uType) :=
  fun (U0 : V0 -> uType) (A : V -> uType) =>
  fun (pA : V0 -> forall v, suptypePattern (A v)) =>
  fun uni : unify (fun v0 v => TryForallArity (U0 v0) Call) pA Call =>
  SuptypePattern (forall v, A v) (TryForallArity (forall v0, U0 v0) uni).
Canonical NoSuptypePattern (A U : uType) (u : U) (hu : U -> call -> hint) :=
  fun fail (fix : fixFail fail) =>
  fun (uni : unify (PostTypeHint ff U u) (hu u pff)) =>
  SuptypePattern A (TryNotSubtype U u uni).

Definition TryOfForallSubtype (U : uType) of U & U & hint := NowUnify.
Definition TryOfPropSubtype (U : uType) u1 u2 :=
  TryOfForallSubtype U u1 u2 NowUnify.
Definition TryOfTypeSubtype := TryOfPropSubtype.
Definition TryOfSameType := TryOfTypeSubtype.

Structure ofSubtype (U : uType) (u1 u2 : U) :=
  OfSubtype { ofSubtype_hint :> hint }.
Canonical OfSameType (U : uType) u1 u2 :=
  OfSubtype U u1 u2 (TryOfSameType U u1 u2).
Canonical OfTypeSubType@{i j | i < j, j < u} (U1 U2 : Type@{i}) :=
  OfSubtype Type@{j} U1 U2 (TryOfTypeSubtype Type@{i} U1 U2).
Canonical OfPropSubType@{j | j < u} (P1 P2 : Prop) :=
  OfSubtype Type@{j} P1 P2 (TryOfTypeSubtype Prop P1 P2).
Canonical OfForallSubtype (V : uType) (U0 U : V -> uType) u01 u02 u1 u2 :=
  fun pU : forall v, ofSubtype (U v) (u1 v) (u2 v) =>
  fun uni : unify (fun v => TryOfTypeSubtype (U0 v) (u01 v) (u02 v)) pU =>
  let hU := TryOfForallSubtype (forall v, U0 v) u01 u02 uni in
  OfSubtype (forall v, U v) u1 u2 hU.

Example RigidReplace {U0 U : uType} : absT -> U0 -> U -> U0. Proof. by []. Qed.
Definition NonRigidReplace {U0 U : uType} := @RigidReplace U0 U.
Structure rigidOpExpr {U : uType} (t : absT) (u : U) : uType :=
  RigidOpExpr { rigidOp_expr : U }.
Add Printing Constructor rigidOpExpr.
Arguments rigidOp_expr {U t u} _.
Arguments RigidOpExpr {U} t u _.

Definition nonRigidSource := @id uType.
Definition nonRigidTarget := @id uType.
Coercion HideRigid {U : uType} (u : nonRigidSource U) : nonRigidTarget U := u.
Arguments HideRigid / {U} u.

Variant appFun (F : uType) : uType := AppFun of F.
Notation get_fun F af := (let: AppFun f := af return F in f).
Arguments AppFun {F} _.

Structure appArg (V F : uType) (af : appFun F) := AppArg { app_arg : V }.
Canonical InferAppArg V F f v := AppArg V F (AppFun f) v.
Arguments appArg V {F} af.
Arguments app_arg {V F af} _.

Structure body (U : uType) : uType := Body { get_body : U }.
Canonical InferBody (U : uType) u := Body U u.

Structure returnType := Return { return_Type :> uType }.
Canonical InferReturn (U : uType) := Return U.

Definition TryReplaceBodyVar@{i} (V : Type@{i}) := @id hint.
Definition TryUseBodyVar V := TryReplaceBodyVar V NowUnify.
Definition TryHideBodyVar := TryUseBodyVar.

CoInductive waste : sType :=
| Waste0
| Waste1 {U : uType} of U
| WasteF {V : uType} of V -> waste
| Waste2 of waste & waste
| Waste4 of waste & waste & waste & waste.

Variant result : sType := Result (rec : hint) (U : uType) (u : U).

Structure subst (t0 t : absT) (w : waste) : sType :=
  Subst { subst_hint :> hint; #[canonical=no] subst_result :> result}.
Arguments subst_result {t0 t w} _.
Definition TryImpredicative (U : uType) := @id U.
Definition TryPredicative := TryImpredicative.
Definition TryForall (U : uType) of U := @id hint.
Definition TryFun (U : uType) u := TryForall U (TryPredicative U u).
Definition TryMaskRigid := TryFun.
Definition TryIf (U : uType) of U := @id hint.
Definition TryApplication := TryIf.
Definition TryReplace := TryApplication.
Definition TrySubstVar := TryReplace.
Definition TryConstant := TrySubstVar.
Definition AppHint (U : uType) u := TryApplication U u NowUnify.
Definition HeadHint (U : uType) (au : appFun U) :=
  let: AppFun u := au in TryConstant U u (TryIf U u NowUnify).
Definition ArgHint (U : uType) u :=
  TryConstant U u (TryIf U u (TryMaskRigid U u NowUnify)).

Structure subsumeProp : sType :=
  SubsumeProp {subsume_Prop :> uType; Prop_subsumption : Prop -> subsume_Prop}.
Canonical PropProp := SubsumeProp Prop id.
Canonical PropSet := SubsumeProp Set id.
Canonical PropType@{i} := SubsumeProp Type@{i} id.

Structure forallPattern@{i} (S S0 : uType) (V0 : Type@{i}) (R0 : V0 -> S)
                            : sType :=
  ForallPattern {
    forall_pattern : S0;
    #[canonical=no] pack_forall (V : Type@{i}) : (V -> S) -> packed
  }.
Arguments pack_forall {S S0 V0 R0} _ V _.

Canonical PredicativeForall@{i} (S : uType := Type@{i}) (V0 : S) R0 :=
  let pR0 : S := TryPredicative S (forall v0, R0 v0 : S) in
  let packS (V : S) R := Pack S (forall v, R v : S) in
  ForallPattern@{i} S S V0 R0 pR0 packS.
Canonical ImpredicativeForall@{i} (S0 : subsumeProp) (V0 : Type@{i}) P0 :=
  let pR0 := TryImpredicative S0 (Prop_subsumption S0 (forall v0, P0 v0)) in
  let packS (V : Type@{i}) P := Pack Prop (forall v, P v : Prop) in
  ForallPattern@{i} Prop S0 V0 P0 pR0 packS.

Section SubstInstances.
Variables t0 t : absT.

Notation subst := (subst t0 t).
Notation Subst := (Subst t0 t).

Variant pattern : sType := Pattern of hint & result.
Coercion SubstPattern w (p : subst w) := Pattern p p.

Canonical Constant (U : uType) u :=
  Subst (Waste1 u) (TryConstant U u NowUnify) (Result NowUnify U u).

Canonical SubstVar (U : uType) (u0 u : U) (pu : ofSubtype U u0 u) :=
  fun pt : unify (TryOfSameType absT t0 t) pu =>
  Subst Waste0 (TrySubstVar U u0 pt) (Result NowUnify U u).

Canonical Replace (U0 U : uType) u0 u :=
  Subst Waste0 (TryReplace U0 (RigidReplace t0 u0 u) NowUnify)
        (Result NowUnify U u).

Canonical MaskRigid (U0 U : uType) u0 u pu0 w (pu : subst w) :=
  fun uni : unify (Pattern (AppHint U0 u0) (Result NowUnify U u)) pu =>
  Subst w (TryMaskRigid U0 (@rigidOp_expr U0 t0 u0 pu0) NowUnify)
          (Result uni U u).

Variant ifData := IfData (pR : bool -> pattern) (pb put puf : pattern).
Canonical IfThenElse@{i} (U0 : Type@{i}) (R0 R : bool -> Type@{i}) :=
  fun u0 fu0 => let hu0 := PostTypeHint fu0 U0 u0 in
  fun b0 u0t u0f => let u0b := if b0 return R0 b0 then u0t else u0f in
  fun mu0 (pfu0 : unifyPost fu0) (uni0 : unify hu0 (mu0 u0b pfu0)) =>
  fun wR (pR : forall b, subst (wR b)) b wb (pb : subst wb) =>
  fun ut wt (put : subst wt) uf wf (puf : subst wf) =>
  let hR b1 :=
    Pattern (ArgHint Type@{i} (R0 b1)) (Result NowUnify Type@{i} (R b1)) in
  let hb := Pattern (ArgHint bool b0) (Result NowUnify bool b) in
  let hu b1 u0 u := Pattern (ArgHint (R0 b1) u0) (Result NowUnify (R b1) u) in
  let h := IfData hR hb (hu true u0t ut) (hu false u0f uf) in
  fun uni : unify h (IfData pR pb put puf) =>
  let u := Result uni (R b) (if b return R b then ut else uf) in
  Subst (Waste4 (WasteF wR) wb wt wf) (TryIf U0 u0 uni0) u.

Canonical HideBodyVar@{i} (VV : Type@{i}) (VR : VV -> Type@{i}) :=
  let V : Type@{i} := forall v, VR v in
  fun wf : V -> waste => let w := Waste2 (WasteF wf) (WasteF wf) in
  let bv v0 v := Body V (HideRigid v) in
  Subst w (TryHideBodyVar V) (Result NowUnify (V -> V -> body V) bv).

Canonical UseBodyVar@{i} (V : Type@{i}) (wf : V -> waste) :=
  let w := Waste2 (WasteF wf) (WasteF wf) in
  Subst w (TryUseBodyVar V) (Result NowUnify (V -> V -> body V) (fun=> Body V)).

Canonical ReplaceBodyVar@{i} (V0 V : Type@{i}) wV wf :=
  let w := Waste2 (Waste2 wV wf) (WasteF (fun v : V => wf)) in
  let hV := Pattern (@ArgHint Type@{i} V0) (Result NowUnify Type@{i} V) in
  fun (pV : subst wV) (uni : unify hV pV) =>
  let bv v0 v := Body V0 (NonRigidReplace t v0 v) in
  Subst w (TryReplaceBodyVar V0 uni) (Result NowUnify (V0 -> V -> body V0) bv).

Variant funData : sType :=
  FunData (V0 V : uType) of pattern & V0 -> V -> pattern.
Arguments FunData {V0 V} _ _.

Definition FunPattern@{i}
    {V0 V : Type@{i}} {R0 : V0 -> uType} {R : V -> uType} :=
  fun f bv0 (bf0 : forall v0, body (R0 v0)) (v0 : V0) (v : V) =>
  let: Body v1 := bv0 v0 v in let: Body u := bf0 v1 in
  Pattern (ArgHint (R0 v1) u) (Result NowUnify (R v) (f v)).
  
Canonical Fun@{i} (V0 V : Type@{i}) (R0 : V0 -> uType) (R : V -> uType) :=
  fun f0 f bv0 bf0 (pbf0 : forall v0, body (bf0 v0)) =>
  let hf := FunPattern f bv0 bf0 in
  let pf0 v0 : R0 v0 := get_body (pbf0 v0) in
  fun uni_f0 : unify f0 pf0 =>
  let hV :=
    Pattern (TryHideBodyVar V0) (Result NowUnify (V0 -> V -> body V0) bv0) in
  fun w wf (pV : subst (Waste2 w (@WasteF V wf))) =>
  fun pf : V0 -> forall v : V, subst (wf v) =>
  fun uni : unify (FunData hV hf) (FunData pV pf) =>
  Subst w (TryFun (forall v0, R0 v0) f0 uni_f0)
                  (Result uni (forall v, R v) f).

Canonical Forall@{i} (V0 V : Type@{i}) (S0 S : uType) R0 U bR0 R bv0 :=
  fun pbR0 : forall v0, markBody (bR0 v0) =>
  let pR0 v0 : S := unmark_body (pbR0 v0) in
  let hV := Pattern (TryHideBodyVar V0) (Pack (V0 -> V -> body V0) bv0) in
  fun w wR (pV : subst (Waste2 w (@WasteF V wR))) =>
  let hR := FunPattern R bv0 bR0 in
  fun pR : V0 -> forall v : V, subst (wR v) =>
  fun uni : unify (FunData R0 hV hR) (FunData pR0 pV pR) =>
  Subst w (TryForall S0 (forall_pattern S S0 V0 R0 U) uni) (pack_forall U V R).

Variant packedApp : sType :=
  PackedApp (V : uType) (oR : V -> uType) (fR : V -> frozen -> uType)
            (R : V -> uType) (af : appFun (forall v, R v)) (av : appArg V af).

Variant appData : sType := AppData (V : uType) (R : V -> uType) of
   V -> hint & packed & forall v, R v & packedApp & pattern & pattern.
(* Arguments AppData {V rR} _ _ _ _ _ _. *)

Canonical Application@{i} (V0 V : Type@{i}) (fV0 : frozen -> Type@{i}) :=
  fun (uV0 : Type@{i} := Force fV0 V0) hR0v (hR0 := fun (_ : uV0) => hR0v) =>
  fun (oR0 uR0 : uV0 -> uType) (fR0 : uV0 -> frozen -> uType) (R : V -> uType)=>
  fun pR0 : forall v0, getArityPattern (fR0 v0) (oR0 v0) (uR0 v0) =>
  fun (uF0 := forall v, uR0 v) (u0f : uF0) (af0 : appFun uF0) =>
  fun av0 : appArg (fV0 Frozen) af0 => let u0v := app_arg av0 in
  fun u0 (hu0 := Pack (fR0 u0v Frozen) u0) (pu0 := Pack (uR0 u0v) (u0f u0v)) =>
  let ho0 := PackedApp uV0 oR0 fR0 uR0 af0 av0 in
  fun (R0 : V0 -> uType) (f0 : forall v0, R0 v0) (v0 : V0) =>
  let oaf0 := AppFun f0 in let oav0 := AppArg V0 (forall v, R0 v) oaf0 v0 in
  let po0 := PackedApp V0 R0 (fun v0 _ => R0 v0) R0 oaf0 oav0 in
  fun f (hf := Pattern (HeadHint f0) (Pack (forall v, R v) f)) =>
  fun v (hv := Pattern (ArgHint v0) (Pack V v)) =>
  fun wf wv (w := Waste2 wf wv) (pf : subst wf) (pv : subst wv) => 
  fun uni : unify (AppData uV0 uR0 hR0 hu0 u0f ho0 hf hv)
                  (AppData uV0 uR0 pR0 pu0 (app_fun af0) po0 pf pv) =>
  Subst w (TryApplication (fR0 u0v Frozen) hR0v u0 uni) (Pack (R v) (f v)).

End SubstInstances.

Structure target (V U : uType) : uType :=
  PackTarget { target_fun :> V -> U; _ : hint}.
Canonical Target {V U : uType} fg := PackTarget V U fg NowUnify.

Structure targetHint (U : uType) (h : hint) : uType :=
  TargetHint { hint_target : U }.
Canonical InferTargetHint (U : uType) u := TargetHint U (ArgHint u) u.

Structure substTarget {V : uType} (U : uType) (g : V -> absT) : uType :=
  SubstTarget { _ : absT -> U; subst_target :> target V U }.
Arguments SubstTarget {V U} g _ _.
Canonical InferSubstTarget V U (f : absT -> U) (g : V -> absT) :=
  fun h ph w (pf : forall t v, subst (g v) t w) =>
  let pu v := hint_target U (h v) (ph v) in
  let hf t v := Pattern (h v) (Pack U (f t)) in
  fun uni : unify hf pf => SubstTarget g f (PackTarget V U pu uni).

Structure comp {V U : uType} (f : absT -> U) (g : V -> absT) :=
  Comp { comp_target :> substTarget U g }.
Canonical FactorComp V U f g :=
  @Comp V U f g (SubstTarget g f (Target (f \o g))).

End HOpattern.

Arguments RigidOpExpr {absT U} t u _.
Arguments NonRigidReplace {absT U0 U} _ _ _.
Arguments comp {absT V U} f g.

Ltac DeclareRigidOp t0 u0 u := let v := fresh "v" in 
  do [intro v; DeclareRigidOp t0 (u0 v) (u v) | exact (RigidOpExpr t0 u u0)].
Notation DeclareRigidOp u0 := 
  (fun T (t0 : T) => ltac:(DeclareRigidOp t0 u0 (NonRigidReplace t0 u0 u0)))
  (only parsing).

Canonical succn_rigid := DeclareRigidOp succn.
Canonical pair_rigid U V := DeclareRigidOp (@pair U V).
Canonical some_rigid U := DeclareRigidOp (@Some U).
Canonical inl_rigid U V := DeclareRigidOp (@inl U V).
Canonical inr_rigid U V := DeclareRigidOp (@inr U V).

Canonical sig_rigid := DeclareRigidOp (@sig).
Canonical sig2_rigid := DeclareRigidOp (@sig2).
Canonical sigT_rigid := DeclareRigidOp (@sigT).
Canonical sigT2_rigid := DeclareRigidOp (@sigT2).
Canonical prod_rigid := DeclareRigidOp prod.
Canonical seq_rigid := DeclareRigidOp seq.
Canonical option_rigid := DeclareRigidOp option.
Canonical sum_rigid := DeclareRigidOp sum.

Lemma foo (D := fun T (_ : T) => True) Z (p1 : Z -> nat)
  (Y := fun b1 b2 => {b0 | b1 || b0 || b2})
  (* (valY := fun b1 b2 (y : Y b1 b2) => sval y) *)
  (vY : forall b1 b2, Y b1 b2 -> bool) (valY := vY)
  (inY := fun b1 b2 b0 (yP : b1 || b0 || b2) => Sub b0 yP : Y b1 b2)
  (eq2 := fun n : nat => 2 == n)
  (H : forall Pn pPn, D {pred nat} Pn /\ D (comp Pn p1) pPn
          -> D {pred Z} pPn) :
(*    D {pred Z} [pred z | valY false (p1 z == 2) (Sub true isT)]. *)
   D {pred Z} [pred z | valY _ _ (if p1 z <= 4 as b return Y b (p1 z == 2)
                  then HideRigid (Sub false isT :> Y true _) else inY false _ true isT)].
Set Debug "unification".  
Set Printing Coercions.
(* Set Printing Existential Instances. *)
Arguments Sub : clear implicits.
Arguments Specif_sig__canonical__eqtype_SubType : clear implicits.
apply: H.
Print Canonical Projections rigidOp_expr.


Set Printing All.
Print Application.

End Subst.

PackTarget { target_fun :> V -> U; _ : T -> V -> call }.
Canonical Target {T U V} (vu0 : V -> U) (tu : T -> U) :=
  @PackTarget T U V vu0 (fun r v => Call (ArgHint (vu0 v)) (tu r))

Definition AppKind {U} of U := Kind.
Definition HeadKind {U} of U := Kind.
Definition ArgKind {U} of U := Kind.

Structure hint := Hint { hint_kind :> kind }.
Notation NoHint := (Hint Kind).

Inductive frame := Frame U & U & kind & seq frame.
Notation stack := (seq frame).

Section Execute. Context {T U V : Type}.
Implicit Types (u : U) (tu : T -> U) (t r : T) (vt : V -> T) (s : stack).

Definition Stack u k u0 s := Frame U u (k u0) s :: s.

Structure step t r u s := Step { step_hint :> hint}.
Structure run t r := Run { run_stack :> stack }.
Structure initStack u := InitStack { init_arg : U; _ : stack; _ : U }.
Structure call t r u u1 := Call { init_stack :> initStack u }.

Structure target :=
  Target { target_expr :> V -> U; _ : V -> U; _ : T -> V -> U }.
Canonical BuildTarget f := Target f [eta f] (fun=> f).

Structure subst vt r u := Subst { subst_in :> target }.
Structure abstract vt tu := Abstract {abstract_in :> target}.

Canonical EndRun t r := Run t r [::].
Canonical StepRun t r u su (pu : step t r u su) (ps : run t r) :=
  Run t r (Frame U u pu su :: ps).

Canonical InitializeStack u0 u s := InitStack u u0 (Stack u ArgKind u0 s) u.
Canonical RunCall t r u0 u u1 (pu : run t r) :=
  Call t r u u1 (InitStack u u0 pu u1).
Canonical RunSubst vt r u u1 (pu : forall v, call (vt v) r u u1) f0 f2 :=
  Subst vt r u1 (Target f0 (fun v => init_arg u (pu v)) f2).
Canonical RunAbstract vt tu (pu : forall r, subst vt r (tu r)) f0 :=
  Abstract vt tu (Target f0 f0 (fun r => subst_in vt r (tu r) (pu r))).

End Execute.

Section SubstHints.
Context {U : Type} (u0 : U) (pu : packedRigid).
Implicit Types (u : U) (pu : packedRigid) (h : hint).
Notation pu0 := (PackType u0).

Definition TryApply pu0 pu1 pu2 h := h.
Notation App h := (TryApply pu0 pu pu h).
Canonical AppHint := App (Hint (AppKind u0)).

Definition TryConstant u0 h := h.
Definition TryReplace u0 h := h.
Definition TryUnmask u0 h := h.
Definition TryIf pu0 pu1 pu2 h := h.
Notation Head h :=
  (TryConstant u0 (TryReplace u0 (TryUnmask u0 (App (TryIf pu0 pu pu h))))).
Canonical HeadHint := Head (Hint (HeadKind u0)).

Definition TryMask u0 h := h.
Definition TryLambda u0 pu1 pu2 h := h.
Canonical ArgHint := Head (TryMask u0 (TryLambda u0 pu pu (Hint (ArgKind u0)))).

End SubstHints.

Section SubstInstances.
Context {T U V : Type}.
Context {vU : V -> Type} {vF : V -> rigidType} {bW : bool -> rigidType}.
Implicit Types (t r : T) (u : U) (v : V).

Canonical Constant t r u := Step t r u [::] (TryConstant u NoHint).

Canonical Replace t r := Step t r r [::] (TryReplace t NoHint).

Canonical Mask t r u u0 su pu0 :=
  Step t r u (Stack u AppKind u0 su) (TryMask (rigidOp_expr t u0 pu0) NoHint).

Canonical Unmask t r u := Step t r u [::] (TryUnmask (LockRigidOp t u) NoHint).

Canonical Lambda t r f f0 sf ps :=
  let s (x : V) := @Stack (vU x) (f x) ArgKind (f0 x) (sf x) in
  let rs (x : V) := run_stack t r (ps x) in
  Step t r f [::] (TryLambda [eta f0] (PackType s) (PackType rs) NoHint).

Canonical IfThenElse t r u b0 vt0 vf0 b vt vf sb st sf :=
  let stf := Stack vt ArgKind vt0 st ++ Stack vf ArgKind vf0 sf in
  let u0 := if b0 return bW b0 then vt0 else vf0 in
  let u' := if b return bW b then vt else vf in
  Step t r u (Stack b ArgKind b0 sb ++ stf) (TryIf (PackRigid u0) u u' NoHint).

Structure wrappedDfun {V} (vF : V -> rigidType) :=
  WrappedFun {unwrap_fun :> forall v : V, vF v}.
Notation wrappedFun V U := (wrappedDfun (fun _ : V => RigidType U)). 
Arguments unwrap_fun {V vF} _.
Arguments WrappedFun {V vF} _.
Canonical WrapFun {V vF} f := @WrappedFun V vF f.

Structure appArg (pf : wrappedDfun vF) (v0 : V) := PackAppArg {arg_of_app : V}.
Canonical AppArg f0 v0 := PackAppArg (WrapFun f0) v0 v0.

Canonical Application t r u f v f0 v0 u1f pf0 pv0 pu0 sf sv :=
  let s := Stack f HeadKind f0 sf ++ Stack v ArgKind v0 sv in
  let pu1 := @PackRigid (vF _) (u1f (arg_of_app pf0 f0 v0 pv0)) in
  Step t r u s (TryApply pu0 pu1 pu0 u1f pf0 u (f v) NoHint).

End SubstInstances.

Lemma foo (D := fun T (_ : T) => True) (p1 : bool -> nat)
  (H : forall Pn pPn, D {pred nat} Pn /\ D (abstract p1 Pn) pPn
          -> D (nat -> {pred bool}) pPn) :
   D (nat -> {pred bool}) (fun=> [pred b | p1 b < 4]).
Set Debug "unification".   
Set Printing Coercions.
Unset Printing Records.
apply: H.
Set Printing All.
Print Application.

End Subst.

Lemma foo (D := fun T (_ : T) => True) (p1 : bool -> nat)
  (H : forall Pn pPn, D {pred nat} Pn /\ D (Subst.abstract p1 Pn) pPn
          -> D (nat -> {pred bool}) (Subst.abstract_in p1 Pn pPn)) :
   D (nat -> {pred bool}) (fun=> [eta [pred b | p1 b < 4]]).
Set Debug "unification".   
Set Printing Coercions.
Unset Printing Records.
refine (H _ _ _).
Print Canonical Projections Subst.unwrap_fun.


Module Export (coercions, canonicals) Subst.
Unset Implicit Arguments.

Structure rigidType := RigidType { rigidType_Type :> Type }.
Canonical SemiflexibleType U := RigidType U.

#[universes(polymorphic)]
Variant packedRigid := PackRigid (T : rigidType) of T.
Arguments PackRigid {T} _.
#[universes(polymorphic)]
Definition PackType {T} (x : T) := @PackRigid (RigidType T) x.

Variant kind := Kind.
Definition AppKind {U} of U := Kind.
Definition HeadKind {U} of U := Kind.
Definition ArgKind {U} of U := Kind.

Structure hint := Hint { hint_kind :> kind }.
Notation NoHint := (Hint Kind).

Inductive frame := Frame U & U & kind & seq frame.
Notation stack := (seq frame).

Section Execute. Context {T U V : Type}.
Implicit Types (u : U) (tu : T -> U) (t r : T) (vt : V -> T) (s : stack).

Definition Stack u k u0 s := Frame U u (k u0) s :: s.

Structure step t r u s := Step { step_hint :> hint}.
Structure run t r := Run { run_stack :> stack }.
Structure initStack u := InitStack { init_arg : U; _ : stack; _ : U }.
Structure call t r u u1 := Call { init_stack :> initStack u }.

Structure target :=
  Target { target_expr :> V -> U; _ : V -> U; _ : T -> V -> U }.
Canonical BuildTarget f := Target f [eta f] (fun=> f).

Structure subst vt r u := Subst { subst_in :> target }.
Structure abstract vt tu := Abstract {abstract_in :> target}.

Canonical EndRun t r := Run t r [::].
Canonical StepRun t r u su (pu : step t r u su) (ps : run t r) :=
  Run t r (Frame U u pu su :: ps).

Canonical InitializeStack u0 u s := InitStack u u0 (Stack u ArgKind u0 s) u.
Canonical RunCall t r u0 u u1 (pu : run t r) :=
  Call t r u u1 (InitStack u u0 pu u1).
Canonical RunSubst vt r u u1 (pu : forall v, call (vt v) r u u1) f0 f2 :=
  Subst vt r u1 (Target f0 (fun v => init_arg u (pu v)) f2).
Canonical RunAbstract vt tu (pu : forall r, subst vt r (tu r)) f0 :=
  Abstract vt tu (Target f0 f0 (fun r => subst_in vt r (tu r) (pu r))).

End Execute.

Section SubstHints.
Context {U : Type} (u0 : U) (pu : packedRigid).
Implicit Types (u : U) (pu : packedRigid) (h : hint).
Notation pu0 := (PackType u0).

Definition TryApply pu0 pu1 pu2 h := h.
Notation App h := (TryApply pu0 pu pu h).
Canonical AppHint := App (Hint (AppKind u0)).

Definition TryConstant u0 h := h.
Definition TryReplace u0 h := h.
Definition TryUnmask u0 h := h.
Definition TryIf pu0 pu1 pu2 h := h.
Notation Head h :=
  (TryConstant u0 (TryReplace u0 (TryUnmask u0 (App (TryIf pu0 pu pu h))))).
Canonical HeadHint := Head (Hint (HeadKind u0)).

Definition TryMask u0 h := h.
Definition TryLambda u0 pu1 pu2 h := h.
Canonical ArgHint := Head (TryMask u0 (TryLambda u0 pu pu (Hint (ArgKind u0)))).

End SubstHints.

Example LockRigidOp {T U} : T -> U -> U. Proof. by []. Qed.
Definition MaskRigidOp {T U} := @LockRigidOp T U.
Structure rigidOpExpr {T U} (t : T) (mu : U) :=
  RigidOpExpr { rigidOp_expr : U }.
Add Printing Constructor rigidOpExpr.

Ltac DeclareRigidOp t mu u := let v := fresh "v" in 
  do [ intro v; DeclareRigidOp t (mu v) (u v) | exact (RigidOpExpr _ _ t mu u)].
Notation DeclareRigidOp u := 
  (fun T (t : T) => ltac:(DeclareRigidOp t (MaskRigidOp t u) u)) (only parsing).

Canonical succn_rigid := DeclareRigidOp succn.
Canonical pair_rigid {U V} := DeclareRigidOp (@pair U V).
Canonical some_rigid {U} := DeclareRigidOp (@Some U).
Canonical inl_rigid {U V} := DeclareRigidOp (@inl U V).
Canonical inr_rigid {U V} := DeclareRigidOp (@inr U V).

Section SubstInstances.
Context {T U V : Type}.
Context {vU : V -> Type} {vF : V -> rigidType} {bW : bool -> rigidType}.
Implicit Types (t r : T) (u : U) (v : V).

Canonical Constant t r u := Step t r u [::] (TryConstant u NoHint).

Canonical Replace t r := Step t r r [::] (TryReplace t NoHint).

Canonical Mask t r u u0 su pu0 :=
  Step t r u (Stack u AppKind u0 su) (TryMask (rigidOp_expr t u0 pu0) NoHint).

Canonical Unmask t r u := Step t r u [::] (TryUnmask (LockRigidOp t u) NoHint).

Canonical Lambda t r f f0 sf ps :=
  let s (x : V) := @Stack (vU x) (f x) ArgKind (f0 x) (sf x) in
  let rs (x : V) := run_stack t r (ps x) in
  Step t r f [::] (TryLambda [eta f0] (PackType s) (PackType rs) NoHint).

Canonical IfThenElse t r u b0 vt0 vf0 b vt vf sb st sf :=
  let stf := Stack vt ArgKind vt0 st ++ Stack vf ArgKind vf0 sf in
  let u0 := if b0 return bW b0 then vt0 else vf0 in
  let u' := if b return bW b then vt else vf in
  Step t r u (Stack b ArgKind b0 sb ++ stf) (TryIf (PackRigid u0) u u' NoHint).

Structure wrappedDfun {V} (vF : V -> rigidType) :=
  WrappedFun {unwrap_fun :> forall v : V, vF v}.
Notation wrappedFun V U := (wrappedDfun (fun _ : V => RigidType U)). 
Arguments unwrap_fun {V vF} _.
Arguments WrappedFun {V vF} _.
Canonical WrapFun {V vF} f := @WrappedFun V vF f.

Structure appArg (pf : wrappedDfun vF) (v0 : V) := PackAppArg {arg_of_app : V}.
Canonical AppArg f0 v0 := PackAppArg (WrapFun f0) v0 v0.

Canonical Application t r u f v f0 v0 u1f pf0 pv0 pu0 sf sv :=
  let s := Stack f HeadKind f0 sf ++ Stack v ArgKind v0 sv in
  let pu1 := @PackRigid (vF _) (u1f (arg_of_app pf0 f0 v0 pv0)) in
  Step t r u s (TryApply pu0 pu1 pu0 u1f pf0 u (f v) NoHint).

End SubstInstances.

Lemma foo (D := fun T (_ : T) => True) (p1 : bool -> nat)
  (H : forall Pn pPn, D {pred nat} Pn /\ D (abstract p1 Pn) pPn
          -> D (nat -> {pred bool}) pPn) :
   D (nat -> {pred bool}) (fun=> [pred b | p1 b < 4]).
Set Debug "unification".   
Set Printing Coercions.
Unset Printing Records.
apply: H.
Set Printing All.
Print Application.

End Subst.

Lemma foo (D := fun T (_ : T) => True) (p1 : bool -> nat)
  (H : forall Pn pPn, D {pred nat} Pn /\ D (Subst.abstract p1 Pn) pPn
          -> D (nat -> {pred bool}) (Subst.abstract_in p1 Pn pPn)) :
   D (nat -> {pred bool}) (fun=> [eta [pred b | p1 b < 4]]).
Set Debug "unification".   
Set Printing Coercions.
Unset Printing Records.
refine (H _ _ _).
Print Canonical Projections Subst.unwrap_fun.

Module Export (coercions, canonicals) Finpred.

Implicit Types I T : eqType. (* We only work with eqTypes. *)

(* Helper notation for the MatchArg utility (see ssreflect.v and ssrfun.v).   *)
Import MatchArgNotation.

(* Labels to distinguish the delimited and undelimited cases. The Delimited   *)
(* label also isolates the predicate and argument. Variants of Undelimited    *)
(* will be declared below to help recover from over-expansion.                *)
Definition Delimited T (P : {pred T}) := P.
Definition Undelimited (Px : bool) := Px.

(* A unit type used to control the triggering of /= (simpl) simplification.   *)
Variant simplTrigger := SimplTrigger.

(* We need to use different structures to infer the (body of) the predicate   *)
(* in the delimited case, which requires a default {pred T} projection, and   *)
(* in the undelimited case, which requires a default bool projection. We      *)
(* implement this by putting the necessary matchPred and matchBody structures *)
(* OUTSIDE the finpred type, which is merely a record with a Finpred.pred     *)
(* projection to {pred T} with no canonical instances.                        *)
(*    We do NOT declare Finpred.pred as the finpred >-> pred_sort coercion;   *)
(* instead we define Finpred.mem : finpred >-> matchPred, so finpred coerces  *)
(* to {pred T} via the matched_pred : matchPred >-> pred_sort projection.     *)
(*    In the delimited case, unifying A : {pred T} with ?F then leads to      *)
(* unifying the default instance MatchAnyPred A with Finpred.mem ?F, which    *)
(* will be resolved by inferring ?F. In the undelimited case, (x \in ?F) will *)
(* reduce to matched_pred (Finpred.mem ?F) x and then further reduce to       *)
(* matched_body (Finpred.pattern ?F x (Finpred.pred ?F x)) where matched_body *)
(* is the bool projection of matchBody. Unifying this term with any Ax : bool *)
(* will then similarly turn into unifying the default matchBody instance      *)
(* MatchAnyBody ?F0 ?x0 ?u Ax with Finpred.pattern ?F x (Finpred.pred ?F x)   *)
(* which will resolve by inferring A and F such that Finpred.pred F = A and   *)
(* A x = ax, setting ?x0 := x and ?F0 := ?F := F (the delimited case also     *)
(* this resolution internally).                                               *)
(*   We ensure that Finpred.mem F : {pred T} simplifies to hook (fun=> id) A  *)
(* when F is a concrete finpred instance for a predicate A, but does NOT      *)
(* simplify when F is an abstract finpred ?F; this is achieved by adding a    *)
(* simplTrigger parameter to the matchPred structure, which then gives its    *)
(* {pred T} projection an additional simplTrigger argument to control its     *)
(* simplification. This argument will be supplied by (the return type of)     *)
(* Finpred.mem, which just projects it from the finpred record, thereby       *)
(* ensuring that if will reduce to the SimplTrigger constructor exactly when  *)
(* F is a concrete instance.                                                  *)
 
(* The interface for feeding a delimited predicate to finpred inference.      *)
(* After unifying P with matched_pred ?mP, which should always succeed, Coq   *)
(* will infer a finpred F for P by unifying the delimited_pred projection of  *)
(* Finpred.mem F with delimited_pred ?mP = [eta Delimited P], then verify     *)
(* that F : {pred T} and P are convertible. As unification proceeds left to   *)
(* right the order of the delimited_pred and matched_pred fields is important *)
(* (indeed inference on the matched_pred projection value will immediately    *)
(* fail as it lacks the Delimited label.                                      *)
Structure matchPred (T : eqType) (t : simplTrigger) := MatchPred {
   #[canonical=no] delimited_pred : {pred T}; (* [eta Delimited matched_pred] *)
   #[reversible=yes] matched_pred :> {pred T} (* for finpred reverse coercion *)
}.
Arguments matched_pred {T !t} _ /. (* simplify only when t ~> Trigger *)
Canonical MatchAnyPred T t P := @MatchPred T t [eta Delimited P] P.
(* The following are needed for Coq < 8.21 where default instances fail to    *)
(* match when extraargs are present. Similar instances should be declared for *)
(* every head constant of the topred projection of a canonical predType       *)
(* instance that is not convertible to predPredType T. These can be listed by *)
(*    Print Canonical Projections topred.                                     *)
(* These extra instances are needed to ensure that finpred matching works     *)
(* consistently in the delimited case, where Coq needs to unify (a \in A)     *)
(* with (v \in ?F) where ?F : {finpred T} is an open evar. Expanding some of  *)
(* the notation Coq is in fact unifying (in_mem a (@mem T pA A)) with         *)
(*  in_mem v (@mem T (predPredType T) (Finpred.matched_pred (Finpred.mem ?F)) *)
(* After unifying a with v, this will only attempt to unify A with            *)
(* (Finpred.matched_pred (Finpred.mem ?F)) if pA, the predType instance for   *)
(* the type of A, is convertible to (predPredType T). If not Coq will then    *)
(* expand mem to expose the Mem constructor on both sides, and then try to    *)
(* unify Mem [eta mA A], where mA is the topred projection of pA, with        *)
(* Mem [eta Finpred.matched_pred (Finpred.mem ?F)], which leads to unifying   *)
(* mA A x with Finpred.matched_pred (Finpred.mem ?F) x for a new variable x.  *)
(* In this case the default MatchAnyPred instance above will NOT be used      *)
(* because of the extra argument x, so we need to provide additional          *)
(* instances, one for each possible mA.                                       *)
Canonical MatchSimplPred T t sP := @MatchAnyPred T t (pred_of_simpl sP).
Canonical MatchMemPred T t mP := @MatchAnyPred T t (pred_of_mem mP).
Canonical MatchMemSeq T t s := @MatchAnyPred T t (mem_seq s).

(* The mixin type for Finpred.type; it provides an upper bound for the        *)
(* support of the predicate projection. All mixin instances will be strictly  *)
(* Qed opaque.                                                                *)
Definition envelope T (P : {pred T}) := {Pbound : seq T | {subset P <= Pbound}}.
Local Notation bpred := pred. (* Will be masked by finpred field name. *)
Record finpred T := Pack {
  trigger : simplTrigger; (* controls reduction of matched_pred (mem F) *)
  pred : {pred T};        (* NOT a coercion to pred_sort *)
  mixin : envelope pred
}.
Arguments mixin {T} A : rename, simpl never. (* Don't expose mixin subproofs. *)
Definition Finpred := Pack^~ SimplTrigger.
Arguments Finpred {T} P e : rename.

(* We support two strategies for inferring a finpred: either we recognize a   *)
(* coercion to {pred T} from a finite container type that coerces to finpred, *)
(* such as seq T or {set T}, in which case we just return that coercion, or   *)
(* we first decompose the boolean expression Px as the application of a       *)
(* predicate P : {pred T} to the argument variable x of the finpred, then     *)
(* traverse P x to infer a finpred F for P. We use the canonical projections  *)
(* to the strategy type declared here to select the strategy to be used.      *)
Variant strategy := TryInferred.
Definition TryContainer := TryInferred. (* Try a container coercion first. *)

(* The memContainer structure is the interface for recognizing membership in  *)
(* a finite container C whose type cT coerces both to {pred T} and finpred.   *)
(* The in_container projection will match applications (C : {pred T}) x of    *)
(* the predicate coercion of C to the variable parameter x, while the F       *)
(* parameter will be used to return the coercion of C to {finpred T}.         *)
(*  Usage: for every type cT that coerces to both {pred T} and {finpred T}    *)
(* declare Canonical cT_Container ... (C : cT ....) := Finpred.Container A.   *)
Structure memContainer T (A : finpred T) (x : T) :=
  MemContainer { in_container :> bool }. (* in_container ~=~ pred F x *)
Notation Container C := (fun x => MemContainer C%FUN x ((C%FUN :> {pred _}) x)).

(* The instances of finpred produced by inference that are not just coercions *)
(* from a finite container type (e.g., finpred_of_seq s) will be of the form  *)
(*   F = Finpred.Inferred F0 (Finpred.Cast P)                                 *)
(* where P is the original predicate and F0 the finpred record inferred by    *)
(* traversing by P x; the type of Inferred ensures that pred_of F0 = P.       *)
(* As Inferred and Cast will be declared as coercions, F will display as P.   *)
Definition cast_source T := {pred T}.
Variant cast {T} : cast_source T -> Type := Cast P : cast P.
Coercion Cast : cast_source >-> cast.
#[warning="-uniform-inheritance"]
Coercion Inferred T (A0 : finpred T) (cast_P : cast (pred A0)) :=
  let transport rT f := let: Cast P in cast P := cast_P return rT P in f P in
  transport (fun P => envelope P -> finpred T) (Pack SimplTrigger) (mixin A0).
Arguments Inferred {T} A0 cast_P.

(* The matchBody structure provides the interface to the unification-based    *)
(* finpred inference algorithm, in addition to a projection to bool with a    *)
(* default instance that will allow us to feed an arbitrary expression to the *)
(* inference algorith, and also serves as a final check that that initial     *)
(* expression is indeed convertible to the inferred finpred applied to the    *)
(* given variable. That interface consists of the inferred finpred, the fresh *)
(* variable the finpred is applied to, and a hint to direct the inference     *)
(* strategy. When performing inference the inferred finpred will be an evar   *)
(* that does NOT have the variable in its scope.                              *)
Structure matchBody T := MatchBody {
  #[canonical=no] inferred_finpred : finpred T;
  #[canonical=no] pred_variable : T;
  #[canonical=no] inference_strategy : strategy;
  matched_body :> bool
}.

(*   The hook composition specialized to T -> bool -> bool and {pred T},      *)
(* to be displayed as a {pred T} >-> {pred T} coercion. Similarly to linear   *)
(* composition f \o g we ensure it is expanded by /= when fully applied.      *)
(*   The identity coercion mentioned in the main header will in fact be       *)
(* hook (fun=> id).                                                           *)
Definition hook_source T := {pred T}.
#[warning="-uniform-inheritance"]
Coercion hook {T} op (P : hook_source T) : {pred T} := fun x => op x (P x).
Arguments hook {T} op P x /.
Lemma hookE T (P : {pred T}) : hook (fun=> id) P = P. Proof. by []. Qed.

(* The matchBody and matchPattern instances that connect an unknown finpred   *)
(* application to the inference algorithm.                                    *)
Definition pattern {T} (A : finpred T) x Ax := MatchBody A x TryContainer Ax.
(* The first occurrence of P is used to infer F in the delimited case, the    *)
(* second one to infer F in the undelimited case.                             *)
#[reversible=yes, warning="-uniform-inheritance"]
Coercion mem {T} (A : finpred T) :=
  let P_A := hook (fun x Ax => matched_body (pattern A x Ax)) (pred A) in
  MatchPred (trigger A) P_A P_A.

Canonical FinpredContainer T (A : finpred T) := Container A.
Canonical PredFinpredContainer T A x := @MemContainer T A x (pred A x).

(* The exact computation of the support from the mixin data is hidden by a    *)
(* submodule signature that uses the finpred >-> pred_sort coercion.          *)
Module Type SupportSignature.
Parameter seq : forall {T}, finpred T -> seq T.
Axiom uniq : forall {T} A, uniq (@seq T A).
Axiom mem : forall {T} A, @seq T A =i A.
End SupportSignature.

Module Support : SupportSignature.
Definition seq T (A : finpred T) := undup (filter [in A] (sval (mixin A))).
Lemma uniq T (A : finpred T) : uniq (seq A). Proof. exact: undup_uniq. Qed.
Lemma mem T (A : finpred T) : seq A =i A.
Proof.
by case: A => t P [b bP] x; rewrite mem_undup mem_filter; apply/andb_idr/bP.
Qed.
End Support.

Notation support := Support.seq.

Lemma eq_support T (A B : finpred T) :
  A =i B <-> perm_eq (support A) (support B).
Proof.
split=> [eqAB | /perm_mem-eqAB x]; last by rewrite -!Support.mem.
by apply/uniq_perm=> [||x]; rewrite ?Support.uniq // !Support.mem eqAB.
Qed.

(* Some basic finpred instances; except for the finpred_of_seq coercion, none *)
(* of these should be returned directly by finpred inferrence; instead, they  *)
(* are the building blocks use to construct the first argument of Inferred.   *)

Program Definition finpred0 {T} := @Finpred T pred0 _.
Next Obligation. by exists nil. Qed.

Program Definition finpred1 {T} a := @Finpred T (pred1 a) _.
Next Obligation. by exists [:: a] => x; rewrite inE. Qed.

Program Definition finpred1x {T} a := @Finpred T [pred x | a == x] _.
Next Obligation. by exists [:: a] => x; rewrite inE eq_sym. Qed.

Program Definition finpredOr {T} (A B : finpred T) :=
  @Finpred T [predU A & B] _.
Next Obligation.
by exists (support A ++ support B) => x; rewrite mem_cat !Support.mem.
Qed.

Program Definition finpredXor {T} (A B : finpred T) :=
  @Finpred T [pred x | (x \in A) (+) (x \in B)] _.
Next Obligation.
exists (support (finpredOr A B)) => x; rewrite Support.mem !inE.
by case: (x \in A).
Qed.

Program Definition finpredAndr {T} (A : finpred T) (P : bpred T) :=
  @Finpred T [pred x in A | P x] _.
Next Obligation. by exists (support A) => x /andP[]; rewrite Support.mem. Qed.

Program Definition finpredAndl {T} (P : bpred T) (A : finpred T) :=
  @Finpred T [pred x | P x & x \in A] _.
Next Obligation. by exists (support A) => x /andP[]; rewrite Support.mem. Qed.

Program Definition finpredIf {T} (P : bpred T) (A B : finpred T) :=
  @Finpred T [pred x | if P x then x \in A else x \in B] _.
Next Obligation.
exists (support (finpredOr A B)) => x; rewrite Support.mem !inE.
by case: ifP => _ ->; rewrite ?orbT.
Qed.

Program
Definition finpredIfl {T} (A : finpred T) (P : bpred T) (B : finpred T) :=
  @Finpred T [pred x | if x \in A then P x else x \in B] _.
Next Obligation.
by exists (support (finpredOr A B)) => x; rewrite Support.mem !inE; case: ifP.
Qed.

Program Definition finpredLeq n := Finpred [pred m | m <= n] _.
Next Obligation. by exists (iota 0 n.+1) => m; rewrite mem_iota. Qed.

Definition seqEnvelope {T} (s : seq T) := envelope s.
Coercion PackSeqEnvelope {T} s (e : @seqEnvelope T s) := Pack SimplTrigger e.
Fixpoint envelope_of_seq {T} (s : seq T) : seqEnvelope s :=
  if s isn't a :: s' then mixin (@finpred0 T) else
  mixin (finpredOr (finpred1 a) (envelope_of_seq s')).
#[warnings="-uniform-inheritance"]
Coercion finpred_of_seq T s : finpred T := @envelope_of_seq T s.
#[warnings="-uniform-inheritance"]
Coercion envelope_of_seq : seq >-> seqEnvelope.
Canonical SeqContainer T (s : seq T) x := Container s x.

(* The structures inferenceProblem, infer, inferOp and matchOp comprise the   *)
(* main interfaces for the recursive inference algorithm.                     *)
(*  - inferenceProblem is the toplevel entry point; unifying the nine         *)
(*    parameters of inferenceProblem specified by the canonical matchBody     *)
(*    instance with the values expected by a canonical instance for its       *)
(*    strategy projection will effectuate the hint's strategy.              *)
(*  - infer is the main recursive entrypoint; it infers a finpred A for a     *)
(*    predicate P guided by a stepHint value.                                 *)
(*  - matchOp is the main branch entry; it proposes candidates for A based on *)
(*    the head constant of the body of P, be it a boolean connective of a     *)
(*    fixed predicate such as <=.                                             *)
(*  - inferOp completes matchOp by selecting an appropriate candidate amongst *)
(*    those proposed by matchOp and calling infer recursively on arguments if *)
(*    matchOp has identified a connective. A inferOp uses the actual value of *)
(*    it can test for constant subexpressions.                                *)
(* There are additional structures defined below to handle finite preimages   *)
(* and predicates over dependent pair (sigma) types.                          *)

Variant constraint := Fail.
Variant constraintTrigger := TriggerConstraint.

Structure solvedConstraint := Solved { solved_constraint :> constraint }.
Implicit Types (c : constraint) (pc : solvedConstraint).

Structure resolve c := Resolve { constraint_trigger : constraintTrigger }.
Canonical TriggeredResolution pc := Resolve pc TriggerConstraint.

Definition Done := Fail.
Canonical SatSuccess := Satisfy Done.

Definition Unify {U1 U2} of U1 & U2 & constraint := @id constraint.
Canonical SatUnify {U} (u : U) pc := Satisfy (Unify u u pc Fail).
Definition Return {U1 U2} u1 u2 := @Unify U1 U2 u1 u2 Done Fail.

(* The P parameter serves two purposes: it enables change-of-variable in the  *)
(* and-sigma case below, and it provides a context ouside of the scope of the *)
(* original predicate variable. Note that A cannot easily play this role as   *)
(* we sometimes need to use an auxiliary structure to select the best way to  *)
(* construct A, in which case the scope restriction is not inherited by the   *)
(* constituents of A.                                                         *)
Variant hint := NoHint.
Structure infer {T} (A : finpred T) (P : {pred T}) :=
  Infer { infer_hint :> hint }.  (* pred A ~=~ P *)

(* The inference of canonical instances of inferOp is guided by the head      *)
(* constant of the predicate body (or the dummy constant boolIf in case of    *)
(* a if-then-else expression) and subject to the resolution of some           *)
(* unification constraints.                                                   *)
Structure inferOp {T} (A : finpred T) (P : {pred T}) (c : constraint) :=
  InferOp { applied_op :> bool }. (* applied_pred = P x for some variable x *)

Structure inferenceProblem {T}
    (A : finpred T) (* the main inference output; the A parameter also *)
                    (* provides the scope constraint for inferring P. *)
    (x : T)         (* a variable that is NOT in scope in either A or P *)
    (pP : '[bool])  (* pattern to infer a P such that '[P x] ~=~ pP *)
    (c : constraint) (* unification constraint to infer A from P (if any) *) :=
  InferenceProblem  { problem_strategy : strategy }.
(* We need to the MatchArg utility fo pP to ensure that in the Container      *)
(* strategy we resolve matched_body as an instance of in_container and not    *)
(* the converse.                                                              *)

(* These are the hints that control the choice of infer instances:            *)
(*  - TryFalse matches only if the predicate body evaluates to false.         *)
(*  - TryOp '[Px] dispatches the inferOp inference on the head constant in    *)
(*    Px : bool. Tryop uses the matchArg facility (see ssreflect.v) to ensure *)
(*    that the applied_op projection has priority should that head constant   *)
(*    be a projection with default instances such as matched_body or          *)
(*    matched_pred.                                                           *)
(*  - TryOp is run a second time with a dummy BoolIf constant; this second    *)
(*    fun will only match the body of P is a boolean if-then-else. We need    *)
(*    the dummy constant because if expressions do not have a head constants  *)
(*    and we need to run this as a second pass to avoid preempting the        *)
(*    instances for the usual bool operators, like orb, which expand to if's. *)
(*  - TryFinType is the final hint that will only match when T is a finite    *)
(*    type (whence every predicate is a finpred).                             *)
Definition TryFalse := @id hint.
Definition TryIf := NoHint.
Definition TryOp of '[bool] := @id hint.
Definition TryOpOrIf of hint & unit := @id hint.
Definition TryFinType := @id hint.
Definition Hint {T} (P : {pred T}) x :=
  TryFalse ((TryOpOrIf (TryOp '[P x] TryIf) tt) (TryFinType NoHint)).

Definition MatchOpArg {T} of finpred T & {pred T} & T -> hint & constraint :=
  Fail.
Definition OpArg {T} A P := @MatchOpArg T A P (Hint P).
Canonical InferOpArg {T} A P pc1 (pA : @infer T A P) pc :=
  Satisfy (MatchOpArg A P (fun=> pA) pc).

Canonical Finpred0 T := Infer (@finpred0 T) pred0 (TryFalse NoHint).
Canonical FinpredOp T A P m pc (pA : @inferOp T A P pc) :=
  Infer A P (TryOp '[pA : bool]_m NoHint).

Definition MatchBodyWith Px Px0 T A x pc pPA :=
  MatchBody A x (@hint_of_problem T A x '[Px] pc pPA) Px0.
Arguments MatchBodyWith Px Px0 [T] A x pc pPA.
Canonical MatchAnyBody Px0 := MatchBodyWith (Undelimited Px0) Px0.

(* The abstractPred structure is the interface for the inference of the P     *)
(* predicate, using either the Delimited label or higher order pattern        *)
(* unification (x is a variable not in scope in P) in the Undelimited case.   *)
(* We record an inferred predicate as [pred x | Px] rather than (fun x => Px).*)
Structure abstractPred T (P : {pred T}) (x : T) :=
  AbstractPred { applied_pred :> bool }.
Canonical AbstractDelimited T P x := @AbstractPred T P x (Delimited P x).
Canonical AbstractUndelimited T P x :=
  @AbstractPred T (SimplPred P) x (Undelimited (P x)).

(* For the Container strategy we do not need the Delimited/Undelimited labels *)
(* or the abstractPred interface as the memContainer instance will provide    *)
(* both predicate and finpred.                                                *)
Canonical SolveContainer T A x m pAx :=
  InferenceProblem A x '[@in_container T A x pAx]_m Done TryContainer.

(* Note that the first ?A ~ ?packP (Cast ?P) unification will filter the      *)
(* context of P to remove x, which will allow the use of higher order pattern *)
(* unification during the inference of pP. Unifying the last two parameters   *)
(* of inferenceProblem will lead to setting ?packP := Inferred A0, hence      *)
(* ?A := Inferred A0 (Cast P), as desired.                                    *)
Canonical SolveInferred {T} A0 x P pack_P m pP :=
  let pA := '[@applied_pred T P x pP]_m in
  let cA := OpArg A0 P (Return (Inferred A0) pack_P) in
  InferenceProblem (pack_P (Cast P)) x pA cA TryInferred.

(* In the undelimited case, Coq will be trying to unify (x \in ?A) ~=~ Ax     *)
(* with ?A : {finpred T} and Ax some arbitrary bool expression in which x may *)
(* occur. If unfolding in (x \in ?A) has priority, e.g., when matching an     *)
(* assumption or conclusion of a lemma, then this will ultimately lead to     *)
(* unifying Ax ~ matched_body (Finpred.pattern ?A x (pred ?A x)) and cause    *)
(* the MatchAnyBody default instance to start inferring ?A from Ax "as is".   *)
(*    However if unfolding in Ax has priority (e.g., when matching a rewrite  *)
(* redex), then Ax will be unfolded down to the last head constant that       *)
(* expands to an irreducible match or fix (setting the rhs_is_stuck flag of   *)
(* evar_conv), before unification even considers expanding x \in ?A. While    *)
(* bool connectives such as andb will be protected by the rhs_is_stuck flag,  *)
(* this will not be the case for relations such as == or <=, and this is      *)
(* likely to spoil finpred inference in such cases.                           *)
(*    We therefore supply some facilities for refolding such relations. We    *)
(* can recognize basic equality predicates such as eqn or eqseq as they are   *)
(* protected by rhs_is_stuck, but we need to beware that equality is often    *)
(* transfered from an injection into another eqType. We can rely on the       *)
(* eqtype.apply_injection volatile label to detect this, and more generally   *)
(* we can use the left hand side of a base type equality to follow the        *)
(* injection chain, and also to detect predicates derived from == such as     *)
(* <=, pred0b, or disjoint.                                                   *)
(*   We use a foldEq structure to implement the chain traversal and folding,  *)
(* along with an UndelimitedEq label to call foldEq from abstractPred. We     *)
(* also use UndelimitedEq when Ax is an && expression, as == on pairs and     *)
(* dependent pairs expand to such expressions; in such cases the call to      *)
(* foldEq may fail, in which case we give up on refolding and fall back to    *)
(* the Undelimited label.                                                     *)
Definition UndelimitedEq T (expanded_eq : bool) (lhs : T) := expanded_eq.
Structure foldEq T (expanded_eq folded_eq : bool) := FoldEq { eq_lhs : T }.

Canonical AbstractUndelimitedEq T T1 P x Px p_y :=
  @AbstractPred T (SimplPred P) x (UndelimitedEq Px (@eq_lhs T1 Px (P x) p_y)).
(* We need to define instances for every head constant of an hasDecEq.eq_op   *)
(* projection, as per Print Canonical Projections hasDecEq.eq_op.             *)
Definition MatchEqBody T y z := MatchBodyWith (@UndelimitedEq T (y == z) y).
Arguments MatchEqBody {T} y z Px0.
Canonical MatchEqop T mT u v := @MatchEqBody T u v (hasDecEq.eq_op mT u v).
Canonical MatchEqb b1 b2 := MatchEqBody b1 b2 (~~ b1 (+) b2).
Canonical MatchOptEq T u v := MatchEqBody u v (@opt_eq T u v).
Canonical MatchSumEq T1 T2 u v := MatchEqBody u v (@sum_eq T1 T2 u v).
Canonical MatchEqn m n := MatchEqBody m n (eqn m n).
Canonical MatchBinNatEq m n := MatchEqBody m n (BinNat.N.eqb m n).
Canonical MatchSeqEq T s1 s2 := MatchEqBody s1 s2 (@eqseq T s1 s2).
Canonical MatchAndBody Px Qx :=
  MatchBodyWith (UndelimitedEq (Px && Qx) Px) (Px && Qx).

(* All canonical instances of foldEq have unfoldable head constants, so if    *)
(* instance arguments or parameters fail to match then unification will fall  *)
(* back on the FoldDefaultEq instance.                                        *)
Canonical FoldDefaultEq T (x y z : T) := FoldEq (x == y) (x == y) z.
Canonical FoldLeq (m n : nat) := FoldEq (m <= n) (m <= n) (m - n)%N.
Canonical FoldInjEq T1 T2 b0 b f p_y :=
  FoldEq b0 b (@eqtype.apply_inj T1 T2 f (@eq_lhs T1 b0 b p_y)).
Canonical FoldSigEq I (T_ : I -> Type) T1 isoT1 b0 b p_u z :=
  FoldEq b0 b (@Sigma.iso.pi1 I T_ T1 isoT1 (@eq_lhs T1 b0 b p_u) == z).

Definition binopPred {T} op (P Q : {pred T}) x : bool := op (P x) (Q x).

Definition InferBinaryOp T F op :=
  fun (A B : finpred T) (P Q : {pred T}) x y =>
  InferOp (F A B) (binopPred op P Q) (OpArg A P (OpArg B Q Done)) (op x y).

Canonical FinpredOr {T} := @InferBinaryOp T finpredOr orb.
Canonical FinpredXor {T} := @InferBinaryOp T finpredXor xorb.

(* The notFinpred structure is the interface for testing whether a bool       *)
(* expression is syntactically unlikey to be the application of a finpred to  *)
(* the predicate variable; the P parameter provides a means of testing for    *)
(* constant expressions that do not depend on the variable.                   *)
(*   The nonfin parameter is used jointly with the MatchArg utility to block  *)
(* spurrious attempts to infer a finpred structure for test_nonfin ?p_nf when *)
(* the tested expression is of the form matched_body (pattern ...) - such an  *)
(* attempt would actually succeed if T were a finType, so every abstract      *)
(* finpred would be classified as "non-finite"!                               *)
(*   We block this by using MatchArg to ensure the test_nonfin projection has *)
(* priority, and providing an instance that lets unfication test_nonfin ?p_nf *)
(* succeed immediately in that case, but sets the nonfin flag to false. We    *)
(* then test the flag in a later argument, when unification has committed to  *)
(* a value for ?p_nf.                                                         *)
Structure notFinpred {T} (nonfin : bool) (P : {pred T}) :=
  NotFinpred {test_nonfin : bool}.
Definition TryConst := @id bool.
Canonical ConstNotFin T a a0 := @NotFinpred T true (fun=> a) (TryConst a0).
Canonical NegbNotFin T P a := @NotFinpred T true P (negb a).
Canonical GeqNotFin T m n r := @NotFinpred T true (fun x => m <= n x) (m <= r).
Canonical MatchedBodyFin T P pb := @NotFinpred T false P (@matched_body T pb).

Definition TestNonFin T of {pred T} & T -> '[bool] & bool & constraint :=
   @id constraint.
Definition NonFinOp T P := @TestNonFin T P (fun x => '[P x]) true.

Canonical InferNonfinOp T P nf p_nf m pc :=
  Satisfy (TestNonFin P (fun=> '[@test_nonfin T nf P p_nf]_m) nf pc Fail).

Canonical FinpredIf T A B C (P Q R : {pred T}) :=
  let P0 x := if P x then Q x else R x in
  let cIf := OpArg B Q (OpArg C R (Return A (finpredIf P B C))) in
  let cIfl := OpArg B P (OpArg C R (Return A (finpredIfl B Q C))) in
  InferOp A P0 (NonFinOp Q cIfl cIf) BoolIf.

(* The SigmaOp label is intended to match predicates over S : Sigma.type I T_ *)
(* which are expressed as a conjunction of predicates over the projections of *)
(* a u : S, more precisely, of the shape (fun u => P (Sigma.pi1 u) && Q u)    *)
(* where P i is a finpred over i : I, and Q (Sigma.dpair i y) is a finpred    *)
(* over y : T_ i for all i : I, where I and T_ is the index and indexed type  *)
(* of S, respectively. In the main use case Q u will further be of the form   *)
(* R (Sigma.pi1 u) (Sigma.pi2 u) where R i will then be a finpred over T_ i.  *)
(*  We intend to support both the case where S is structurally a dependent    *)
(* pair type (e.g., S = T1 * T2), and the case where S is a type that is      *)
(* indexed by Sigma.pi1 and T_ is a subType of S, e.g., S = seq T, pi1 = size *)
(* T_ n = n.-tuple T. However support for the latter case will require some   *)
(* extension of Coq.                                                          *)
(*   The P above need to be inferred by matching the Ppi1 parameter, whose    *)
(* value will be [preim Sigma.pi1 of P]. The next two parameters are the      *)
(* hints for recursively inferring a finpred A for P and a finpred B i        *)
(* parametrized by i : I for [preim Sigma.dpair i of Q]. The last parameter   *)
(* is a copy of Q and is used to ensure that the finpred F obtained by        *)
(* combining A and B is actually a finpred for (fun u => Ppi1 u && Q u) and   *)
(* not (fun u => Ppi1 u && Q (dpair (pi1 u) (pi2 u))). We can always use      *)
(* Sigma.eta to reduce the latter case, by to do so we need to pass a copy of *)
(* Q ot the finpred combinator, thus duplicating it in the finpred expression *)
(* since B will essentially also be a copy of Q. This will not be usually     *)
(* necessary (e.g., when Q = R (pi1 u) (pi2 u), or S = seq T), so we use      *)
(* unification with this copy of Q to select the correct finpred combinator.  *)
Import Subst (abstractIn, AbstractIn, abstract).
Definition MatchSigmaOp {T I} (A : finpred T) (Q : {pred T}) :=
  fun of abstractIn I T & T -> hint & I -> T -> hint & {pred T} =>
  @id constraint.
(* A label for the last {pred T} argument of SigmaOp; the corresponding       *)
(* canonical value avoids an unneeded eta-reduction; if this fails the label  *)
(* argument will become a parameter of the eta-reducing finpred combinator.   *)
Definition TryNoEta T := @id {pred T}.
Definition SigmaOp {T} I A P Q :=
  @MatchSigmaOp T I A Q (AbstractIn P) (Hint P) (fun=> Hint Q) (TryNoEta Q).

(* Note that I will only be instantiated when matching the SigmaOp label;     *)
(* otherwise I is left uninstatiated, but this is of no consequence as cSigma *)
(* will then not appear in the inferred inferOp canonical instance.           *)
Canonical FinpredAnd T I A B (P Q : {pred T}) Px Qx :=
  let cAndl := NonFinOp P (OpArg B Q (Return A (finpredAndl P B))) in
  let cAndr := OpArg B P (Return A (finpredAndr B Q)) in
  InferOp A (binopPred andb P Q) (cAndl (SigmaOp I A P Q cAndr)) (Px && Qx).

Section Sigma.

Context (I : eqType) (T_ : I -> eqType)  (S : Sigma.eqType I T_).
Import Sigma (pi1, pi2, dpair).
Implicit Types (B : finpred I) (C : forall i, finpred (T_ i)).
Implicit Types (P : {pred I}) (Q : {pred S}) (R : forall i, {pred T_ i}).
Let Rpair Q i := [preim dpair i of Q].
Let Renvelope R := forall i, envelope (R i).
Let Rpi R := [pred u : S | R (pi1 u) (pi2 u)].

(* The structure factorPi1 P factors pi1 out of its {pred S} projection Ppi1, *)
(* i.e., it finds P such that Ppi1 == (preim pi1 P).                          *)
(*   Ideally, this operation should notrequire a structure, as it is an       *)
(* obvious extension of higher-order unification, which is indeed implemented *)
(* by, e.g, Hol Light. The second-best alternative would be to use the Elpi   *)
(* unification entry point and do the substitution Elpi. A Typeclass/Ltac     *)
(* solution would be need a similar entry point for typeclass resolution;     *)
(* currently, even with the Typeclass Resolution For Conversion flag set      *)
(* Typeclass resolution will only happen between calls to unification from    *)
(* type inference so it cannot provide timely information during unification. *)
(* Finally, a pure Canonical Structure partial solution, using CS resolution  *)
(* to traverse the applicative part of Ppi1 u that depends on u to compute P  *)
(* (maybe allowing fun) would require a means of reliably matching an         *)
(* arbitrary application f a, which the currenf Coq unification heuristics do *)
(* not provide. It treats the obvious pattern ?f ?a as a higher order pattern *)
(* for which it defers resolution, thus making it useless for traversal.      *)
(* There is a workaround using as CS with a default projection value, e.g.,   *)
(* unwrap ?wf ?a, but it is blocked by the faulty extraarg computation for    *)
(* default projection instances.                                              *)
(*   The temporary solution adopted here is use an auxiliary structure        *)
(* substDpair R to unify (Rpair Ppi1) with R = (fun i _ => P i). When S is a  *)
(* structural sigma type then pi1 (dpair i y) will reduce to i so if indeed   *)
(* Ppi1 = P \o pi1 the two terms will be convertible. However the       *)
(* unification can still fail as Coq does not fully reduce a term to check a  *)
(* variable (here, y) does not occur in it; it does do head reduction, which  *)
(* is enough to recognize the abstract form of [predX A & B].                 *)

(* The combineSigma structure is used to select the appropriate finpred       *)
(* combination A of the finpred B of the left hand side predicate P, and of   *)
(* the parametrized finpred C i of the right hand side predicate Rpair Q i.   *)
(* It has output parameter A, and input parameters B, C, as well as the       *)
(* predicate R i and the envelope mixin eC i of C i. Its {pred S} projection  *)
(* is the original right hand side predicate Q, initially labeled with        *)
(* TryNoEta, and is used with R to first test whether no explicit eta is      *)
(* needed (because eta holds by conversion), and if this fails to incorporate *)
(* eta reduction in the construction of A.                                    *)
Structure combineSigma (A : finpred S) B C R (eC : Renvelope R) :=
  CombineSigma { sigma_pi2_pred :> {pred S} }.

(* The no-eta case. *)
Program Definition finpredSigma B C :=
  @Finpred S [pred u | pi1 u \in B & pi2 u \in C (pi1 u)] _.
Next Obligation.
exists [seq dpair i y | i <- support B, y <- support (C i)] => u.
rewrite !inE => /andP[Bu1 Cu2]; apply/allpairsPdep.
by exists (pi1 u), (pi2 u); split; rewrite (Support.mem, Sigma.eta).
Qed.
Canonical FinpredSigma B C R eC :=
  @CombineSigma (finpredSigma B C) B C R eC (TryNoEta (Rpi R)).

(* Use eta reduction on the right hand side. *)
Program Definition finpredSigmaEta B Q (eC : Renvelope (Rpair Q)) :=
  @Finpred S [pred u | pi1 u \in B & u \in Q] _.
Next Obligation.
exists (support (finpredSigma B (fun i => Finpred (Rpair Q i) (eC i)))) => u.
by rewrite Support.mem !inE Sigma.eta.
Qed.
Canonical FinpredSigmaEta B C Q eC :=
  @CombineSigma (finpredSigmaEta B eC) B C (Rpair Q) eC Q.

(* The resolution of the SigmaOp constraint; note the four canonical          *)
(* structure resolution sub-calls for B, C, P and A.                          *)
Canonical InferSigmaOp A B C P Q (pP : abstract pi1 P) :=
  fun (pB : infer B P) (pC : forall i, infer (C i) (Rpair Q i)) =>
  fun  (pA : combineSigma A B C (fun i => mixin (C i))) =>
  Satisfy (MatchSigmaOp A Q pP (fun=> pB) (fun i _ => pC i) pA Fail).

End Sigma.

(* The finPreimFun and finPreimOp records are assembled to construct a linear *)
(* sized representation of an expression f x with a finite pre image - i.e.,  *)
(* such that for any given y, f x = y for only finitely many x. Both allow    *)
(* for hook composition, i.e., for stray occurrences of the predicate         *)
(* variable x outside of the argument(s) of the function or operator. For     *)
(* example one record for +%N represents expressions y + g x where y is to be *)
(* instantiated with an expression with finite preimage.                      *)
Definition unaryOpPreimBound {T0 T1 T} (h : T0 -> T1 -> T) :=
  {b : T -> seq T1 | forall x y, y \in b (h x y)}.
Definition binaryOpPreimBound {T0 T1 T2 T} (h : T0 -> T1 -> T2 -> T) :=
  {b : T -> seq T1 * seq T2 |
   forall x y1 y2, let (b1, b2) := b (h x y1 y2) in (y1 \in b1) || (y2 \in b2)
  }.
Record preimUnaryOp T0 T1 T := PreimUnaryOp {
  preim_unary_op :> T0 -> T1 -> T;
  preim_unary_op_bounded : unaryOpPreimBound preim_unary_op
}.
Arguments PreimUnaryOp {T0 T1 T} _ _.
Record preimBinaryOp T0 T1 T2 T := PreimBinaryOp {
  preim_binary_op :> T0 -> T1 -> T2 -> T;
  preim_binary_op_bounded : binaryOpPreimBound preim_binary_op
}.
Arguments PreimBinaryOp {T0 T1 T2 T} _ _.
Definition preimFun T0 T := preimUnaryOp T0 T0 T.
Definition preim_fun {T0 T} (f : preimFun T0 T) x := f x x.
Coercion preim_fun : preimFun >-> Funclass.
Definition PreimFun T0 T f b : preimFun T0 T := PreimUnaryOp (fun=> f) b.
Arguments PreimFun {T0 T} f b.

(* Factories for preimOp. *)
Program Definition PcanPreimOp T0 {T1 T} (f : T1 -> T) g (fK : pcancel f g) :=
  PreimUnaryOp (fun _ : T0 => f) _.
Next Obligation. by exists (seq_of_opt \o g) => _ y /=; rewrite fK inE. Qed.
Arguments PcanPreimOp T0 {T1 T} f g fK.
Definition CanPreimOp T0 {T1 T} (f : T1 -> T) g (fK : cancel f g) :=
  PcanPreimOp T0 f (Some \o g) (can_pcan fK).
Arguments CanPreimOp T0 {T1 T} f g fK.
Definition PreimId T : preimFun T T := CanPreimOp T id id (frefl _).

Program Definition ComposePreimUnaryOp {T0 T1 T} :=
  fun (h : preimUnaryOp T0 T1 T) (f : preimFun T0 T1) =>
  PreimFun (fun x => h x (f x)) _.
Next Obligation.
case: h f => h [b bh] [f [b1 b1f]] /=.
by exists (flatten \o map b1 \o b) => _ x; apply/flatten_mapP; exists (f x x).
Qed.

Program Definition ComposePreimBinaryOp {T0 T1 T2 T} :=
  fun (h : preimBinaryOp T0 T1 T2 T) =>
  fun (f1 : preimFun T0 T1) (f2 : preimFun T0 T2) =>
  PreimFun (fun x => h x (f1 x) (f2 x)) _.
Next Obligation.
case: h f1 f2 => h [b bh] [f1 [b1 b1f]] [f2 [b2 b2f]] /=.
exists (fun z => flatten (map b1 (b z).1) ++ flatten (map b2 (b z).2)) => _ x.
rewrite mem_cat; apply/orP; case: (b _) (bh x (f1 x x) (f2 x x)) => bh1 bh2 /=.
by do [case/orP; [left | right]; apply/flatten_mapP];
   [exists (f1 x x) | exists (f2 x x)].
Qed.

Lemma NatPreimUnaryOpBound T0 T (h : T0 -> nat -> T) :
  {b | forall x n, n <= b (h x n)} -> unaryOpPreimBound h.
Proof.
case=> b bh; exists (fun y => iota 0 (b y).+1) => x n.
by rewrite mem_iota ltnS bh.
Qed.

Definition NatPreimUnaryOp T0 T h b :=
  PreimUnaryOp h (@NatPreimUnaryOpBound T0 T h b).

Lemma NatPreimBinaryOpBound T0 T (h : T0 -> nat-> nat -> T) :
  {b | forall x n1 n2, minn n1 n2 <= b (h x n1 n2)} -> binaryOpPreimBound h.
Proof.
case=> b bh; pose bs z := iota 0 (b z).+1.
exists (fun z => (bs z, bs z)) => x n1 n2 /=.
by rewrite !mem_iota /= !ltnS -geq_min.
Qed.

Definition NatPreimBinaryOp T0 T h b :=
  PreimBinaryOp h (@NatPreimBinaryOpBound T0 T h b).

(* Optimize the function expression by eliding the identity finPreim. *)
Structure compPreim {T0 T1 T} (h : preimUnaryOp T0 T1 T) (hf : preimFun T0 T) :=
  CompPreim { compPreim_rhs :> preimFun T0 T1 }.
Canonical compPreimWithId {T0 T} (f : preimFun T0 T) :=
  CompPreim f f (PreimId T0).
Canonical compPreimWithFun {T0 T1 T} (h : preimUnaryOp T0 T1 T) f :=
  CompPreim h (ComposePreimUnaryOp h f) f.

Structure inferPreim {T0 T} (f : preimFun T0 T) (g : T0 -> T) c :=
  InferPreim { preim_body : T }.

Canonical InferPreimId {T} x := InferPreim (PreimId T) id Done x.

Definition MatchPreimArg {T0 T} of preimFun T0 T & T0 -> T & T0 -> T :=
  fun of constraint => Fail.
Definition TryVal {T} := @id T.
Definition PreimArg {T0 T} f g := @MatchPreimArg T0 T f g (TryVal \o g).
Canonical InferPreimArg {T0 T} f g pc1 pf pc2 :=
  Satisfy (MatchPreimArg f g (fun=> @preim_body T0 T f g pc1 pf) pc2).

Definition InferPreimUnaryOp {T0 T1 T} (h : preimUnaryOp T0 T1 T) hxy :=
  fun (f : preimFun T0 T) (pf : compPreim h f) (g1 : T0 -> T1) =>
  InferPreim f (fun x => h x (g1 x)) (PreimArg pf g1 Done) hxy.
Arguments InferPreimUnaryOp {T0 T1 T} h hxy f pf g1.

Fixpoint SomePreimUnaryOp {T0 T1 T} g pf g1 (hs : seq (preimUnaryOp T0 T1 T)) :=
  if hs isn't h :: hs' then Fail else let hg x := h x (g1 x) in
  Unify g hg (PreimArg (pf h) g1 Done) (SomePreimUnaryOp g pf g1 hs').
Definition InferSomePreimUnaryOp {T0 T1 T} hs hxy :=
  fun (f : preimFun T0 T) g (pf : forall h, compPreim h f) g1 =>
  InferPreim f g (@SomePreimUnaryOp T0 T1 T g [eta pf] g1 hs) hxy.
Arguments InferSomePreimUnaryOp {T0 T1 T} hs hxy f g pf g1.

Definition InferPreimBinaryOp {T0 T1 T2 T} (h : preimBinaryOp T0 T1 T2 T) hxy :=
  fun f1 f2 => let hf := ComposePreimBinaryOp h f1 f2 in
  fun g1 g2 => let hg x := h x (g1 x) (g2 x) in
  InferPreim hf hg (PreimArg f1 g1 (PreimArg f2 g2 Done)) hxy.
Arguments InferPreimBinaryOp {T0 T1 T2 T} h hxy f1 f2 g1 g2.

Definition preim_val T0 T P (S : subEqType P) :=
  @PcanPreimOp T0 S T val _ valK.
Canonical InferPreim_val {T0 T P} (S : @subEqType T P) (y : S) :=
  InferPreimUnaryOp (preim_val T0 S) (TryVal (val y)).

Program Definition finpred_preim T0 T (f : preimFun T0 T) (A : finpred T) :=
  Finpred [preim f of A] _.
Next Obligation.
case: f => f [b bf] /=; exists (flatten (map b (support A))) => x Afx.
by apply/flatten_mapP; exists (f x x); rewrite ?Support.mem.
Qed.

Structure preimOf {T0 T} (Af : finpred T0) (A : finpred T) :=
  PreimOf { preimOf_fun :> preimFun T0 T }.
Canonical PreimOfId T A := PreimOf A A (PreimId T).
Canonical PreimOfFun T0 T A f := @PreimOf T0 T (finpred_preim f A) A f.

Definition InferPreimOf {T0 T} A label Pf Af b :=
  fun (pAf : @preimOf T0 T Af A) (pf : forall x, inferPreim pAf x) =>
  InferOp Af Pf (label Pf (fun x => matched_preim (pf x)) (MatchOp b)).

Definition PreimOp {T0 T} of finpred T & {pred T0} & T0 -> T := @id matchOp.
Canonical InferPreimOp {T0 T} A := @InferPreimOf T0 T A (PreimOp A).

Definition InOp {T0 T} of {pred T} & stepHint & {pred T0} & T0 -> T :=
  @id matchOp.
Canonical Finpred_in {T0 T} (f : T0 -> T) (P : {pred T}) y0 :=
  let Pf x := f x \in P in
  InOp P (TryFalse (P y0)) Pf (f \o TryVal) (MatchOp (y0 \in P)).
Canonical InferInOp {T0 T} P A (pA : @infer T A P) :=
  @InferPreimOf T0 T A (InOp P pA).

Definition FinpredPred {T} p0 A T0 f :=
  @PreimOp T0 T A (fun x => pred A (f x)) (f \o TryVal) p0.
Definition OneFinpredPred {T} b0 := @FinpredPred T (MatchOp b0).
Fixpoint ManyFinpredPred {T} b0 As T0 (f : T0 -> T) :=
  if As isn't A :: As' then MatchOp b0 else
  FinpredPred (ManyFinpredPred b0 As' f) A f.

Canonical Finpred_finpred {T} y0 (A : finpred T) :=
  OneFinpredPred (matched_pred (mem A) y0) A.
Canonical Finpred_seq {T} (s : seq T) y0 :=
  OneFinpredPred (mem_seq s y0) (finpred_of_seq s).
Canonical Finpred_leq m0 n := OneFinpredPred (m0 <= n) (finpredLeq n).
Canonical Finpred_eq {T} (a x0 y0 : T) :=
  ManyFinpredPred (x0 == y0) [:: finpred1 a; finpred1x a].

Definition preim_pair T0 T1 T2 (y1 : T1) :=
  @CanPreimOp T0 T2 _ (pair y1) snd (frefl _).
Canonical Preim_pair T0 T1 T2 x (y1 : T1) (y2 : T2) :=
  OnePreimUnaryOp x (preim_pair T0 T2 y1) y2 (y1, y2).

Definition preim_Tagged T0 I (T_ : I -> eqType) i :=
  PcanPreimOp T0 (@Tagged I i T_) otagged_at TaggedK.
Canonical Preim_Tagged T0 x I (T_ : I -> eqType) i y :=
  OnePreimUnaryOp x (preim_Tagged T0 T_ i) y (Tagged T_ y) .

Definition preim_Tagged2 T0 I (T1_ T2_ : I -> eqType) i y1 :=
  PcanPreimOp T0 (@Tagged2 I i T1_ T2_ y1) _ Tagged2K.
Canonical Preim_Tagged2 T0 x I (T1_ T2_ : I -> eqType) i (y1 : T1_ i) y2 :=
  OnePreimUnaryOp x (preim_Tagged2 T0 T2_ y1) y2 (Tagged2 T1_ T2_ y1 y2). 

Definition preim_succn T0 := @CanPreimOp T0 _ _ succn predn (frefl _).
Canonical Preim_succn T0 x n := OnePreimUnaryOp x (preim_succn T0) n n.+1.

Program Definition preim_predn T0 := @NatPreimUnaryOp T0 _ (fun=> predn) _.
Next Obligation. by exists succn => _ []. Qed.
Canonical Preim_predn T0 x y := OnePreimUnaryOp x (preim_predn T0) y y.-1.

Program Definition preim_addnl T0 m_ :=
  @NatPreimUnaryOp T0 _ (fun x n => n + m_ x) _.
Next Obligation. by exists id => x n; apply: leq_addr. Qed.
Program Definition preim_addnr T0 m :=
  @NatPreimUnaryOp T0 _ (fun _ n => m + n) _.
Next Obligation. by exists id => x n; apply: leq_addl. Qed.
Canonical Preim_addn T0 m m_ x n m0 n0 :=
  ManyPreimUnaryOps x n (m0 + n0) [:: preim_addnr T0 m; preim_addnl m_].

Definition preim_double T0 := @CanPreimOp T0 _ _ double half doubleK.
Canonical FinPreim_double A x n := OneFinPreimApp x n n.*2 (finPreim_double A).

Program Definition finPreim_half A :=
  @FinPreim_nat A _ (fun=> half) (fun n => n.*2.+1) _.
Next Obligation. by rewrite -leq_half_double. Qed.
Canonical FinPreim_half A x n := OneFinPreimApp x n (half n) (finPreim_half A).

Definition finPreim_mulnl A m_ :=
  @FinPreim_nat A _ (fun x n => n * (m_ x).+1) id
                    (fun _ _ => @leq_pmulr _ _.+1 isT).
Definition finPreim_mulnr A m :=
  @FinPreim_nat A _ (fun x n => m.+1 * n) id (fun _ _ => leq_addr _ _).
Canonical FinPreim_muln A m m_ x n m0 n0 :=
  ManyFinPreimApp x n (m0 * n0) [:: finPreim_mulnr A m; finPreim_mulnl m_].

Program Definition finPreim_expnl A m_ :=
  @FinPreim_nat A _ (fun x n => n ^ (m_ x).+1) id _.
Next Obligation. by case: n => //= n; rewrite expnS leq_pmulr // expn_gt0. Qed.
Program Definition finPreim_expnr A n2 :=
  @FinPreim_nat A _ (fun x m => n2.+2 ^ m) id _.
Next Obligation. by case: n => //= b; rewrite ltnW 1?ltn_expl. Qed.
Canonical FinPreim_expn A m n2 x n m0 n0 :=
  ManyFinPreimApp x n (m0 ^ n0) [:: finPreim_expnr A n2; finPreim_expnl m].

Definition finPreim_maxnl A m_ :=
  @FinPreim_nat A _ (fun x n => maxn n (m_ x)) id (fun _ _ => leq_maxl _ _).
Definition finPreim_maxnr A m :=
  @FinPreim_nat A _ (fun x n => maxn m n) id (fun _ _ => leq_maxr _ _).
Canonical FinPreim_maxn A m m_ x n m0 n0 :=
  ManyFinPreimApp x n (m0 * n0) [:: finPreim_maxnr A m; finPreim_maxnl m_].

Definition LabelPreimFinpred {A T : eqType}
   (Pf : {pred A}) (P P0 : {pred T}) (f : A -> T) := @id labeled_bool.
Definition LabelOnePreimFinpred {A T : eqType} pT op in_pT (P : pT) f y0 P0 :=
  @LabelPreimFinpred A T (fun x => op (f x) P) (in_pT P)
    (fun y => TryFalse (in_pT P y)) (fun x => TryVar (f x))
    (LabelBool (op y0 P0)).
Canonical InferPreimFinpred {A T : eqType} c (Pf : {pred A}) (P : {pred T}) F Ff
         (eF : T -> inferFinpred P F) (eFf : forall x, inferFinPreim F Ff x) :=
  OpFinpred Pf Ff
     (LabelPreimFinpred Pf P [eta eF] (fun x => finPreim_val (eFf x)) c).
Canonical Finpred_in {A T} P f y0 P0 :=
  @LabelOnePreimFinpred A T (mem_pred T) in_mem pred_of_mem P f y0 P0.

Structure finPreimOp (A B1 B2 T : eqType) := FinPreimOp {
  finPreim_op :> A -> B1 -> B2 -> T;
  finPreimOp_bounded : {b : T -> seq B1 * seq B2
    | forall x y1 y2 (bxy := b (finPreim_op x y1 y2)),
        (y1 \in bxy.1) || (y2 \in bxy.2)}}.
Program Definition FinPreimOp_nat A T h b
   (hb : forall x m1 m2, minn m1 m2 <= b (h x m1 m2)) :=
  @FinPreimOp A _ _ T h _.
Next Obligation.
pose bs z := iota 0 (b z).+1; exists (fun z => (bs z, bs z)) => x m1 m2 /=.
by rewrite !mem_iota /= !ltnS -geq_min.
Qed.

Definition LabelFinPreimAppOp {A B1 B2 T} (h : finPreimOp A B1 B2 T)
           (x : A) (z z0 : labelFinPreimExpr T x) (y1 : B1) (y2 : B2) := z0.
Definition OneFinPreimOp {A B1 B2 T} x y1 y2 hxy (h : finPreimOp A B1 B2 T) :=
  let z := LabelFinPreimExpr x (h x y1 y2) in
  LabelFinPreimAppOp h z (LabelFinPreimExpr x hxy) (TryVal y1) (TryVal y2).
Fixpoint ManyFinPreimOps {A B1 B2 T} x y1 y2 hxy hs :=
  if hs isn't h :: hs' then LabelFinPreimExpr x hxy else
  let z := LabelFinPreimExpr x (@finPreim_op A B1 B2 T h x y1 y2) in
  let z0 := ManyFinPreimOps x y1 y2 hxy hs' in
  LabelFinPreimAppOp h z z0 (TryVal y1) (TryVal y2).

Program Definition ComposeFinPreimOp {A B1 B2 T} (h : finPreimOp A B1 B2 T)
  (g1 : finPreimFun A A B1) (g2 : finPreimFun A A B2) :=
  @FinPreimFun A A T (fun x y => h x (g1 x y) (g2 x y)) _.
Next Obligation.
case: h g1 g2 => h [b hb] [g1 [b1 gb1]] [g2 [b2 gb2]] /=.
exists (fun z => flatten (map b1 (b z).1) ++ flatten (map b2 (b z).2)) => x y.
set y1 := g1 x y; set y2 := g2 x y; set z := h x y1 y2.
rewrite mem_cat; apply/orP; case/orP: (hb x y1 y2) => bz; [left | right].
  by apply/flatten_mapP; exists (g1 x y).
by apply/flatten_mapP; exists (g2 x y).
Qed.
Canonical InferFinPreimCompOp {A B1 B2 T} h g1 g2 x
     (y1 : inferFinPreimApp g1 x) (y2 : inferFinPreimApp g2 x) z :=
  InferFinPreimApp (ComposeFinPreimOp h g1 g2)
    (@LabelFinPreimAppOp A B1 B2 T h x z z
       (finPreim_expr y1) (finPreim_expr y2)).

Definition finPreim_minn A :=
  @FinPreimOp_nat A nat (fun=> minn) id (fun _ _ _ => leqnn _).
Canonical FinPreim_minn A x y1 y2 :=
  OneFinPreimOp x y1 y2 (minn y1 y2) (finPreim_minn A).

(******************************************************************************)
(*************************** Unit Tests          ******************************)
(******************************************************************************)


(*Definition t1 (T : choiceType) (A : {set T}) : finPred T :=
  [pred x in A]. *)

(*
Lemma foo (D := fun T (x : T) => True)
  (G : forall (T : eqType) A, D {finpred T} A -> D {pred T} A)
  (T : eqType) (a b : T) (P Q : {finpred T}) :
   D {pred _} [pred x : {n | 5 < n} | sval x == 3].
Set Printing All.
Set Debug "unification".
refine (G _ _ _).
Abort.
Lemma foo (a : T) A B (D := fun U (z : U) => Prop) : True.
Set Printing Coercions.
Close Scope coerced_scope.
Undelimit Scope coerced_scope.
Set Printing Width 160.
Set Printing Implicit.
Set Debug "unification".
*)

(*
Lemma foo (D := fun T (x : T) => True) (T : eqType) (a b : T)
  (G : forall T A, D {finpred T} A -> D {pred T} A) :
   D {pred _} [pred x | x.1 == a & x.2 == b].
apply: G.
by [].
Print Canonical Projections S.
suff G1 L: D (labelFinPreimExpr _ N) L -> D nat (finPreim_expr L).
have: D nat N.+1.
Set Printing All.
have bar A m n : @FinPreim_succ A m n = @FinPreim_IDN A m n.
  congr LabelFinPreimApp.

Label
Lemma foo (D := fun T (x : T) => True) (T : eqType)
  (G : forall A, D {finpred nat} A -> D {pred nat} A) :
   D {pred nat} [pred n | n < N].
refine (G _ _).
Print Canonical Projections S.
suff G1 L: D (labelFinPreimExpr _ N) L -> D nat (finPreim_expr L).
have: D nat N.+1.
Set Printing All.
have bar A m n : @FinPreim_succ A m n = @FinPreim_IDN A m n.
  congr LabelFinPreimApp.

Label
split.
refine (G1 _ _).
Print Canonical Projections IDN.
have: D _ FinPreim_succ.
rewrite /FinPreim_succ.
rewrite /OneFinPreimApp.
rewrite {1}/finPreim_succ.
rewrite /CanFinPreim /PcanFinPreim.
 simpl.
have: D _ FinPreim_succ.
rewrite /FinPreim_succ.
rewrite /OneFinPreimApp. simpl.
refine (G _ _).

have: D (finpred T) pred0.

refine (P _ _ _).
have: D _ [in s].
refine (P _ _).
rewrite /in_mem.  /=.
apply: P.
Definition D {T} (x : T) := True.
Set Printing Implicit.
Lemma foo2 (T : eqType) (x : T) 
           (P : forall A : {finpred T}, D A -> x \in A) : False.
suff Q (L : labeled_pred T) : D L -> x \in L.
have foo (A : {finpred T}) : x \in [pred x in A | x == x].
eapply Q.
Show Existentials.
*)

Definition t1' (T : choiceType) (P : finpred T) : {finpred T} :=
  [pred x in P] : {pred T}.
Definition t2 (T : choiceType) (P : {finpred T}) (Q : pred T) : finpred T :=
  [pred x | ([in P] x) && (Q x)].
Fail Definition t3 (T : choiceType) (A : {set T}) (Q : pred T) : finpred T :=
   [pred x | (x \in A) && (Q x)].
Definition t4 (T : choiceType) (P : finpred T) (Q : finpred T) : finpred T :=
   [pred x | (x \in P) || (x \in Q)].
Fail Definition t5 (T : finType) (P : pred T) : finpred T :=
   [pred x | P x].
Definition def (T : choiceType) (P Q : {pred T}) : pred T := [pred x : T | P x && Q x].
Definition t6 (T : choiceType) (P : finpred T) Q : finpred T :=
   [pred x : T | def P Q x ].

Fail Check fun (T : choiceType) (P : finpred T) => [eta P] : finpred T.
Fail Check fun (T : choiceType) (P : finpred T) => [in P] : finpred T.
Fail Check fun (T : choiceType) (A : {set T}) => [in A] : finpred T.
Fail Check fun (T : choiceType) (P : finpred T) (Q : pred T) =>
   (fun x => (P x) && (Q x)) : finpred T.
Fail Check fun (T : choiceType) (A : {set T}) (Q : pred T) =>
   (fun x => (x \in A) && (Q x)) : finpred T.
Fail Check fun (T : choiceType) (P : finpred T) (Q : finpred T) =>
   (fun x => (P x) || (Q x)) : finpred T.

Fail Check fun (T : choiceType) (P : finpred T) (Q : pred T) =>
  enum [pred x in P | Q x].

Fail Check fun (T : choiceType) (A : {set T}) => enum A.

(* Some operator definitions. *)

HB.lock Definition card {T} P := size (@support T P).
Canonical card_unlockable := Unlockable card.unlock.

(* A is at level 99 to allow the notation #|G : H| in groups. *)
Reserved Notation "#| A |" (at level 0, A at level 99, format "#| A |").
Notation "#| A |" := (card ((*pred_set*) A)) (only parsing): nat_scope.  (* TODO *)
Notation "#| A |" := (card A) (only printing): nat_scope.

Definition pred0b {T} P := @card T P == 0.

HB.lock Definition enum {T : choiceType} P := sort prec_eq (@support T P).
Canonical enum_unlockable := Unlockable enum.unlock.
Definition pick {T} P := ohead (@enum T P).
Definition pick_pred {T} := @id {pred T}.

Notation "[ 'pick' x | P ]" := (pick (pick_pred (fun x => P%B)))
  (at level 0, x name, format "[ 'pick'  x  |  P  ]") : form_scope.
Notation "[ 'pick' x : T | P ]" := (pick (pick_pred (fun x : T => P%B)))
  (at level 0, x name, only parsing) : form_scope.
Definition pick_true T (x : T) := true.
Reserved Notation "[ 'pick' x : T ]"
  (at level 0, x name, format "[ 'pick'  x : T ]").
Notation "[ 'pick' x : T ]" := [pick x : T | pick_true x]
  (only parsing) : form_scope.
Notation "[ 'pick' x : T ]" := [pick x : T | pick_true _]
  (only printing) : form_scope.
Notation "[ 'pick' x ]" := [pick x : _]
  (at level 0, x name, only parsing) : form_scope.
Notation "[ 'pick' x | P & Q ]" := [pick x | P && Q ]
  (at level 0, x name,
   format "[ '[hv ' 'pick'  x  |  P '/ '   &  Q ] ']'") : form_scope.
Notation "[ 'pick' x : T | P & Q ]" := [pick x : T | P && Q ]
  (at level 0, x name, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A ]" := [pick x | x \in A]
  (at level 0, x name, format "[ 'pick'  x  'in'  A  ]") : form_scope.
Notation "[ 'pick' x : T 'in' A ]" := [pick x : T | x \in A]
  (at level 0, x name, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A | P ]" := [pick x | x \in A & P ]
  (at level 0, x name,
   format "[ '[hv ' 'pick'  x  'in'  A '/ '   |  P ] ']'") : form_scope.
Notation "[ 'pick' x : T 'in' A | P ]" := [pick x : T | x \in A & P ]
  (at level 0, x name, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A | P & Q ]" := [pick x in A | P && Q]
  (at level 0, x name, format
  "[ '[hv ' 'pick'  x  'in'  A '/ '   |  P '/ '  &  Q ] ']'") : form_scope.
Notation "[ 'pick' x : T 'in' A | P & Q ]" := [pick x : T in A | P && Q]
  (at level 0, x name, only parsing) : form_scope.

(******************************************************************************)
(*************************** fintype starts here ******************************)
(******************************************************************************)

Definition disjoint (T : eqType) (A : finpred T) (mB : mem_pred T) :=
  @pred0b T [pred x in A | in_mem x mB].

Notation "[ 'disjoint' A & B ]" := (disjoint A (mem B))
  (at level 0,
   format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'") : bool_scope.

HB.lock
Definition subset (T : eqType) (A : finpred T) (mB : mem_pred T) : bool :=
  pred0b [pred x in A | ~~ (in_mem x mB)].
Canonical subset_unlock := Unlockable subset.unlock.

Notation "A \subset B" := (subset A (mem B))
  (at level 70, no associativity) : bool_scope.

Definition proper (T : eqType) (A B : finpred T) :=
  (A \subset B) && ~~ (B \subset A).
Notation "A \proper B" := (proper A B)
  (at level 70, no associativity) : bool_scope.

(* image, xinv, inv, and ordinal operations will be defined later. *)

Section EqOpsTheory.
Variable T : eqType.
Implicit Types (A B C : {finpred T}) (F : finpred T) (P Q : {pred T}).
Implicit Types (x : T) (s : seq T).

Variant pick_spec (P : pred T) : option T -> Type :=
  | Pick x of P x         : pick_spec P (Some x)
  | Nopick of P =i xpred0 : pick_spec P None.

Lemma eq_card A B : A =i B -> #|A| = #|B|.
Proof. by rewrite unlock => /eq_support/perm_size. Qed.

Lemma eq_pred0b A B : A =i B -> pred0b A = pred0b B.
Proof. by unfold pred0b => /eq_card->. Qed.

Lemma eq_card_trans A B n : #|A| = n -> B =i A -> #|B| = n.
Proof. by move=> <- /eq_card. Qed.

Lemma card_uniqP s : reflect (#|s| = size s) (uniq s).
Proof.
rewrite (uniq_size_uniq (support_uniq s) (mem_support _)) eq_sym unlock.
exact: eqP.
Qed.

Lemma card0 : #|@pred0 T| = 0. Proof. exact/(card_uniqP [::]). Qed.

Lemma card1 x : #|pred1 x| = 1.
Proof. by rewrite -(@eq_card [:: x]) => [|y /[!inE]//]; apply/card_uniqP. Qed.

Lemma eq_card0 A : A =i pred0 -> #|A| = 0.
Proof. exact: eq_card_trans card0. Qed.

Lemma eq_card1 x A : A =i pred1 x -> #|A| = 1.
Proof. exact: eq_card_trans (card1 x). Qed.

Lemma cardUI A B : #|[predU A & B]| + #|[predI A & B]| = #|A| + #|B|.
Proof.
pose U := [predU A & B].
have Dcard C: {subset C <= U} -> #|C| = count [in C] (support U).
  move=> sCU; rewrite unlock -size_filter; apply/perm_size.
  rewrite uniq_perm ?filter_uniq // => x.
  by rewrite mem_filter !inE andb_idr // => /sCU.
rewrite !{}Dcard ?count_predUI // => x /[!inE]; try case/andP; move=> -> //.
exact: orbT.
Qed.

Lemma cardID P A : #|[predI A & P]| + #|[pred x in A | x \notin P]| = #|A|.
Proof.
rewrite -cardUI addnC [in LHS]eq_card0 => [|x] /=.
  by apply: eq_card => x /[!inE]/=; rewrite -andb_orr orbN andbT.
by rewrite !inE andbACA andbN andbF.
Qed.

Lemma cardU1 x A : #|[predU1 x & A]| = (x \notin A) + #|A|.
Proof.
case Ax: (x \in A); first by apply/eq_card => y /[!inE]; case: eqP => // ->.
rewrite /= -(card1 x) -cardUI addnC.
by rewrite [in RHS]eq_card0 // => y /[!inE]; case: eqP => // ->.
Qed.

(* notes:

today:
Lemma cardU1 (T : finType) (x : T) (A : {pred T}) : #|[predU1 x & A]| = (x \notin A) + #|A|.

options for the future:
Lemma cardU1 (T : choiceType) (x : T) (A : finPred T) :
  #|[predU1 x & A]| = (x \notin A) + #|A|.
Lemma cardU1 (T : choiceType) (x : T) A S (_ : finPred_aux T [predU1 x & A] S) :
  #|S| = (x \notin A) + #|A|.
rewrite cardU1. (* works no matter how you derive the finiteness of [predU1 x & A] \*)

*)

Lemma card2 x y : #|pred2 x y| = (x != y).+1.
Proof. by rewrite cardU1 inE card1 addn1. Qed.
(* The cardU1 match succeeds but exposes a finpred1 y structure, as it        *)
(* matches the finpred structures directly, and the inner finpred1 is not     *)
(* labeled by a call to reverse_coercion.                                     *)

Lemma cardD1 x A : #|A| = (x \in A) + #|[predD1 A & x]|.
Proof.
apply/(@addnI (x \notin A)); rewrite addnA addn_negb -cardU1.
have <-: x \notin [predD1 A & x] = 1 :> nat by rewrite !inE eqxx.
by rewrite -cardU1; apply/eq_card=> y /[!inE]; rewrite orb_andr orbN.
Qed.

Lemma card_undup s : #|undup s| = #|s|.
Proof. by apply/eq_card=> x; rewrite !inE mem_undup. Qed.

Lemma card_size s : #|s| <= size s.
Proof.
by rewrite unlock (uniq_leq_size (support_uniq _))// => x /[!inE].
Qed.

Lemma card0_eq A : #|A| = 0 -> A =i pred0.
Proof. by move=> + x; apply/contra_eqF=> Ax; rewrite (cardD1 x) Ax. Qed.

Lemma card0P A : reflect (forall x, x \notin A) (#|A| == 0).
Proof.
apply: (iffP eqP) => [A0 x|A0]; first by rewrite card0_eq.
by apply/eq_card0=> x; apply/idPn/A0.
Qed.

Lemma card_gt0P A : reflect (exists x, x \in A) (#|A| > 0).
Proof.
apply: (iffP idP) => [|[x]]; last by rewrite lt0n; apply/contraL=> /card0P->.
by rewrite unlock -has_predT => /hasP[x /[!inE]]; exists x.
Qed.

Lemma pred0P A: reflect ((A : {pred T}) =1 pred0) (pred0b A).
Proof. by apply: (iffP eqP); [apply: card0_eq | apply: eq_card0]. Qed.

Lemma pred0Pn A : reflect (exists x, x \in A) (~~ pred0b A).
Proof. by rewrite -lt0n; apply: card_gt0P. Qed.

Lemma card_le1P {A} : reflect {in A, forall x, A =i pred1 x} (#|A| <= 1).
Proof.
rewrite leq_eqVlt ltnNge orbC; case: posnP => [A0 | Agt0].
  by apply/ReflectT=> x; rewrite card0_eq.
apply/(iffP idP)=> A1; last by case/card_gt0P: Agt0 => x /A1/eq_card1->.
move=> x xA y; rewrite (cardD1 x) xA in A1; have{A1} := card0P _ A1 y.
by rewrite !inE; case: eqP => [->|_ /negbTE].
Qed.

Lemma mem_card1 A : #|A| = 1 -> {x | A =i pred1 x}.
Proof.
move=> A1; suffices [x xA]: {x | x \in A}.
  by exists x; apply/(card_le1P _ x xA); rewrite A1.
rewrite unlock in A1; case defA: (support A) A1 => // [x s] _.
by exists x; rewrite -mem_support defA mem_head.
Qed.

Lemma card1P A : reflect (exists x, A =i pred1 x) (#|A| == 1).
Proof.
by apply: (iffP idP) => [/eqP/mem_card1[x inA]|[x /eq_card1/eqP//]]; exists x.
Qed.

Lemma card_le1_eqP A :
  reflect {in A &, forall x, all_equal_to x} (#|A| <= 1).
Proof.
apply: (iffP card_le1P) => [Ale1 x y /Ale1-> /eqP // | all_eq x xA y].
by apply/idP/eqP=> [/(all_eq x y xA) | ->].
Qed.

Lemma subsetE A P : (A \subset P) = pred0b [predD A & P].
Proof. by rewrite unlock; apply/eq_pred0b => /= x; rewrite inE andbC. Qed.

Lemma subsetP A P : reflect {subset A <= P} (A \subset P).
Proof.
rewrite unlock; apply: (iffP (pred0P _)) => [AP0 x | sAP x] /=.
  by apply/implyP/idPn; rewrite negb_imply [_ && _]AP0.
by rewrite -negb_imply; apply/negbF/implyP/sAP.
Qed.

Lemma subsetPn A P :
  reflect (exists2 x, x \in A & x \notin P) (~~ (A \subset P)).
Proof.
rewrite unlock; apply: (iffP (pred0Pn _)) => [[x] | [x Ax P'x]].
  by case/andP; exists x.
by exists x; rewrite /= inE P'x andbT.
Qed.

Lemma subset_leq_card A B : A \subset B -> #|A| <= #|B|.
Proof.
move=> sAB; rewrite -(cardID A B) (@eq_card _ A) ?leq_addr// => x.
by rewrite !inE andbC; case Ax: (x \in A) => //; apply: subsetP Ax.
Qed.

Lemma subxx F : F \subset F.
Proof. exact/subsetP. Qed.
Hint Resolve subxx : core.

Lemma eq_subset A B : A =i B -> forall P, (A \subset P) = (B \subset P).
Proof.
by move=> eqAB C; rewrite !unlock; apply: eq_pred0b => /= x; rewrite !inE eqAB.
Qed.

Lemma eq_subset_r P Q : P =i Q -> forall A, (A \subset P) = (A \subset Q).
Proof.
by move=> eqPQ A; rewrite !unlock; apply/eq_pred0b => x; rewrite !inE eqPQ.
Qed.

Lemma eq_subxx A P : A =i P -> A \subset P.
Proof. by move/eq_subset_r <-. Qed.

Lemma subset_predT F : F \subset T.
Proof. exact/subsetP. Qed.

Lemma subset_pred1 P x : (pred1 x \subset P) = (x \in P).
Proof. by apply/subsetP/idP=> [-> | Px y /eqP->] //; apply: eqxx. Qed.

Lemma subset_eqP A B : reflect (A =i B) ((A \subset B) && (B \subset A)).
Proof.
apply: (iffP andP) => [[sAB sBA] x| eqAB]; last by rewrite !eq_subxx.
by apply/idP/idP; apply: subsetP.
Qed.

Lemma subset_cardP A B : #|A| = #|B| -> reflect (A =i B) (A \subset B).
Proof.
move=> eqcAB; case: (subsetP A B) (subset_eqP A B) => //= sAB.
case: (subsetP B A) => [//|[]] x Bx; apply: contraFT (ltnn #|A|) => A'x.
rewrite [leqRHS]eqcAB (cardD1 x B) Bx ltnS.
by apply/subset_leq_card/subsetP=> y Ay; rewrite inE (memPn A'x) ?sAB.
Qed.

Lemma subset_leqif_card A B : A \subset B -> #|A| <= #|B| ?= iff (B \subset A).
Proof.
move=> sAB; split; [exact: subset_leq_card | apply/eqP/idP].
  by move/subset_cardP=> sABP; rewrite (eq_subset_r (sABP sAB)).
by move=> sBA; apply: eq_card; apply/subset_eqP; rewrite sAB.
Qed.

Lemma subset_trans A B P : A \subset B -> B \subset P -> A \subset P.
Proof. by move/subsetP=> sAB /subsetP=> sBP; apply/subsetP=> x /sAB/sBP. Qed.

Lemma subset_all s P : (s \subset P) = all [in P] s.
Proof. exact: (sameP (subsetP s P) allP). Qed.

Lemma subset_cons s x : s \subset x :: s.
Proof. by apply/(subsetP s) => y /[!inE] ->; rewrite orbT. Qed.

Lemma subset_cons2 s1 s2 x : s1 \subset s2 -> x :: s1 \subset x :: s2.
Proof.
move=> ?; apply/(subsetP (x :: s1)) => y /[!inE]; case: eqP => // _.
exact: (subsetP s1).
Qed.

Lemma subset_catl s s' : s \subset s ++ s'.
Proof. by apply/(subsetP s)=> x xins; rewrite mem_cat xins. Qed.

Lemma subset_catr s s' : s \subset s' ++ s.
Proof. by apply/(subsetP s) => x xins; rewrite mem_cat xins orbT. Qed.

Lemma subset_cat2 s1 s2 s3 : s1 \subset s2 -> s3 ++ s1 \subset s3 ++ s2.
Proof.
move=> /(subsetP s1) s12; apply/(subsetP (s3 ++ s1)) => x.
by rewrite !mem_cat => /orP[->|/s12->]; rewrite ?orbT.
Qed.

Lemma filter_subset P s : [seq a <- s | P a] \subset s.
Proof. by apply/subsetP=> x; rewrite mem_filter => /andP[]. Qed.

Lemma subset_filter P s1 s2 :
  s1 \subset s2 -> [seq a <- s1 | P a] \subset [seq a <- s2 | P a].
Proof.
move/subsetP=> s12; apply/subsetP=> x.
by rewrite !mem_filter => /andP[-> /s12].
Qed.

Lemma properE A B : A \proper B = (A \subset B) && ~~ (B \subset A).
Proof. by []. Qed.

Lemma properP A B :
  reflect (A \subset B /\ (exists2 x, x \in B & x \notin A)) (A \proper B).
Proof. by rewrite properE; apply: (iffP andP) => [] [-> /subsetPn]. Qed.

Lemma proper_sub A B : A \proper B -> A \subset B.
Proof. by case/andP. Qed.

Lemma proper_subn A B : A \proper B -> ~~ (B \subset A).
Proof. by case/andP. Qed.

Lemma proper_trans A B C : A \proper B -> B \proper C -> A \proper C.
Proof.
case/properP=> sAB [x Bx nAx] /properP[sBC [y Cy nBy]].
rewrite properE (subset_trans sAB) //=; apply/subsetPn; exists y => //.
by apply: contra nBy; apply: subsetP.
Qed.

Lemma proper_sub_trans A B C : A \proper B -> B \subset C -> A \proper C.
Proof.
case/properP=> sAB [x Bx nAx] sBC; rewrite properE (subset_trans sAB) //.
by apply/subsetPn; exists x; rewrite ?(subsetP _ _ sBC).
Qed.

Lemma sub_proper_trans A B C : A \subset B -> B \proper C -> A \proper C.
Proof.
move=> sAB /properP[sBC [x Cx nBx]]; rewrite properE (subset_trans sAB) //.
by apply/subsetPn; exists x => //; apply: contra nBx; apply: subsetP.
Qed.

Lemma proper_card A B : A \proper B -> #|A| < #|B|.
Proof.
by case/andP=> sAB nsAB; rewrite ltn_neqAle !(subset_leqif_card sAB) andbT.
Qed.

Lemma proper_irrefl A : ~~ (A \proper A).
Proof. by rewrite properE subxx. Qed.

Lemma properxx A : (A \proper A) = false.
Proof. by rewrite properE subxx. Qed.

Lemma eq_proper A B : A =i B -> proper A =1 proper B.
Proof.
move=> eAB C; congr (_ && _); first exact: (eq_subset eAB).
by rewrite (eq_subset_r eAB).
Qed.

Lemma eq_proper_r A B : A =i B -> (@proper T)^~ A =1 (@proper T)^~ B.
Proof.
move=> eAB C; congr (_ && _); first exact: (eq_subset_r eAB).
by rewrite (eq_subset eAB).
Qed.

Lemma card_geqP {A n} :
  reflect (exists s, [/\ uniq s, size s = n & {subset s <= A}]) (n <= #|A|).
Proof.
apply: (iffP idP) => [n_le_A|[s] [uniq_s size_s /(subsetP s) subA]]; last first.
rewrite -size_s -(card_uniqP _ uniq_s).
  exact: (subset_leq_card subA).
exists (take n (support A)); rewrite take_uniq ?support_uniq // size_take.
split=> //; last by move=> x /mem_take; rewrite mem_support.
case: (ltnP n (size (support A))) => // size_A.
by apply/eqP; rewrite eqn_leq size_A /=; rewrite unlock in n_le_A.
Qed.

Lemma card_gt1P A :
  reflect (exists x y, [/\ x \in A, y \in A & x != y]) (1 < #|A|).
Proof.
apply: (iffP card_geqP) => [[s] []|[x] [y] [xA yA xDy]].
  case: s => [|a [|b []]]//= /[!(inE, andbT)] aDb _ subD.
  by exists a, b; rewrite aDb !subD ?inE ?eqxx ?orbT.
by exists [:: x; y]; rewrite /= !inE xDy; split=> // z /[!inE] /pred2P[]->.
Qed.

Lemma card_gt2P A :
  reflect (exists x y z,
              [/\ x \in A, y \in A & z \in A] /\ [/\ x != y, y != z & z != x])
          (2 < #|A|).
Proof.
apply: (iffP card_geqP) => [[s] []|[x] [y] [z] [[xD yD zD] [xDy xDz yDz]]].
  case: s => [|x [|y [|z []]]]//=; rewrite !inE !andbT negb_or -andbA.
  case/and3P => xDy xDz yDz _ subA.
  by exists x, y, z; rewrite xDy yDz eq_sym xDz !subA ?inE ?eqxx ?orbT.
exists [:: x; y; z]; rewrite /= !inE negb_or xDy xDz eq_sym yDz; split=> // u.
by rewrite !inE => /or3P [] /eqP->.
Qed.

Lemma disjoint_sym A B : [disjoint A & B] = [disjoint B & A].
Proof. by congr (_ == 0); apply: eq_card => x; apply: andbC. Qed.

Lemma eq_disjoint A B : A =i B -> forall P, [disjoint A & P] = [disjoint B & P].
Proof.
by move=> eqAB C; congr (_ == 0); apply: eq_card => x /=; rewrite !inE eqAB.
Qed.

Lemma eq_disjoint_r P Q :
  P =i Q -> forall A, [disjoint A & P] = [disjoint A & Q].
Proof.
by move=> eqPQ A; congr (_ == 0); apply: eq_card => x /=; rewrite !inE eqPQ.
Qed.

Lemma subset_disjoint A P : (A \subset P) = [disjoint A & [predC P]].
Proof.
apply/subsetP/pred0P => [sAP x | + x] /=.
  by rewrite -negb_imply; apply/negbF/implyP=> /sAP.
by move/(_ x)/negbT; rewrite /= -negb_imply negbK => /implyP.
Qed.

Lemma disjoint_subset A P : [disjoint A & P] = (A \subset [predC P]).
Proof.
by rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite !inE negbK.
Qed.

Lemma disjointFr A P x : [disjoint A & P] -> x \in A -> x \in P = false.
Proof. by move/pred0P/(_ x) => /= + Ax; rewrite Ax. Qed.

Lemma disjointFl A P x : [disjoint A & P] -> x \in P -> x \in A = false.
Proof. by move/pred0P/(_ x) => /= + Px; rewrite Px andbT. Qed.

Lemma disjointWl A B P : A \subset B -> [disjoint B & P] -> [disjoint A & P].
Proof. by rewrite 2!disjoint_subset; apply: subset_trans. Qed.

Lemma disjointWr A P B : A \subset P -> [disjoint B & P] -> [disjoint B & A].
Proof.
rewrite 2!disjoint_subset => /subsetP-sAB /subsetP-sPB'.
by apply/subsetP => x /sPB'; apply/contra/sAB.
Qed.

Lemma disjointW A B C P :
  A \subset B -> C \subset P -> [disjoint B & P] -> [disjoint A & C].
Proof. by move=> sAB sCP B'P; apply/(disjointWl sAB)/(disjointWr sCP). Qed.

Lemma disjoint0 P : [disjoint pred0 & P].
Proof. exact/pred0P. Qed.

Lemma eq_disjoint0 A P : A =i pred0 -> [disjoint A & P].
Proof. by move/eq_disjoint->; apply: disjoint0. Qed.

Lemma disjoint1 x P : [disjoint pred1 x & P] = (x \notin P).
Proof.
apply/pred0P/idP=> [/(_ x) /= /[!(inE, eqxx)] /= -> // | + y].
by apply/contraNF=> /andP[/eqP<-].
Qed.

Lemma eq_disjoint1 x A P : A =i pred1 x ->  [disjoint A & P] = (x \notin P).
Proof. by move/(@eq_disjoint _ (pred1 x))->; apply: disjoint1. Qed.

Lemma disjointU A B P :
  [disjoint [predU A & B] & P] = [disjoint A & P] && [disjoint B & P].
Proof.
case: [disjoint A & P] / (altP (pred0P [predI A & P])) => [A0|] /=.
  by apply/eq_pred0b => x; rewrite !inE andb_orl [_ && _]A0.
apply/contraNF=> /= /pred0P-nABC; apply/pred0P=> x /=.
by apply: contraFF (nABC x); rewrite /= andb_orl => ->.
Qed.

Lemma disjointU1 x A P :
  [disjoint [predU1 x & A] & P] = (x \notin P) && [disjoint A & P].
Proof. by rewrite (disjointU (pred1 x)) disjoint1. Qed.

Lemma disjoint_cons x s P :
  [disjoint x :: s & P] = (x \notin P) && [disjoint s & P].
Proof. exact: (disjointU1 x [pred x | x \in s] P). Qed.

Lemma disjoint_has s P : [disjoint s & P] = ~~ has [in P] s.
Proof.
apply/negbRL; apply/pred0Pn/hasP => [[x /andP[]]|[x]]; exists x => //.
exact/andP.
Qed.

Lemma disjoint_cat s1 s2 P :
  [disjoint s1 ++ s2 & P] = [disjoint s1 & P] && [disjoint s2 & P].
Proof. by rewrite !disjoint_has has_cat negb_or. Qed.

End EqOpsTheory.

Lemma map_subset {T T' : eqType} (s1 s2 : seq T) (f : T -> T') :
  s1 \subset s2 -> [seq f x | x <- s1 ] \subset [seq f x | x <- s2].
Proof.
move=> /(subsetP s1) s1s2; apply/(subsetP (map _ _)) => _ /mapP[y]/[swap]-> ys1.
by apply/mapP; exists y => //; apply: s1s2.
Qed.

#[global] Hint Resolve subxx : core.

Arguments pred0P {T A}.
Arguments pred0Pn {T A}.
Arguments card_le1P {T A}.
Arguments card_le1_eqP {T A}.
Arguments card1P {T A}.
Arguments subsetP {T A P}.
Arguments subsetPn {T A P}.
Arguments subset_eqP {T A B}.
Arguments card_uniqP {T s}.
Arguments card_geqP {T A n}.
Arguments card_gt0P {T A}.
Arguments card_gt1P {T A}.
Arguments card_gt2P {T A}.
Arguments properP {T A B}.

Section ChoiceOpsTheory.
Variable T : choiceType.
Implicit Types (A B : {finpred T}).
Implicit Types (x : T).

Lemma mem_enum A : enum A =i A.
Proof. by rewrite unlock => x; rewrite mem_sort inE. Qed.

Lemma enum_uniq (A : finpred T) : uniq (enum A).
Proof. by rewrite unlock sort_uniq. Qed.
Hint Resolve enum_uniq : core.

Lemma enum0 : enum pred0 = Nil T.
Proof.
by apply: size0nil; move: (@card0 T); rewrite !unlock size_sort.
Qed.

Lemma enum1 x : enum (pred1 x) = [:: x].
Proof.
apply: perm_small_eq => //; apply: uniq_perm => // y.
by rewrite mem_enum /= !inE.
Qed.

Lemma pickP A : pick_spec (A : {pred T}) (pick (pick_pred A)).
Proof.
rewrite /pick; case: (enum _) (mem_enum A) => [|x s] Axs /=.
  by right; apply: fsym.
by left; rewrite -[_ x]Axs mem_head.
Qed.

(* Should we keep it? *)
Definition set_pickP A : pick_spec [in A] (pick A) := pickP A.

Lemma enum_prec_eq_sorted (A : finpred T) : sorted prec_eq (enum A).
Proof. by rewrite unlock sort_sorted//; apply: prec_eq_total. Qed.
Local Hint Resolve enum_prec_eq_sorted : core.

Lemma eq_enum A B : A =i B -> enum A = enum B.
Proof.
move=> AB; apply: (@sorted_eq _ prec_eq) => //.
- exact: prec_eq_trans.
- exact: prec_eq_antisymmetric.
by apply: uniq_perm => // x; rewrite !mem_enum.
Qed.

Lemma eq_pick A B :
  (A : {pred T}) =1 (B : {pred T}) -> pick (pick_pred A) = pick (pick_pred B).
Proof. by rewrite /pick => /eq_enum->. Qed.

Lemma cardE A : #|A| = size (enum A).
Proof. by rewrite !unlock size_sort. Qed.

End ChoiceOpsTheory.
#[export] Hint Extern 0 (is_true (uniq (enum _))) =>
  solve [apply: enum_uniq] : core.

(**********************************************************************)
(*                                                                    *)
(*  Boolean injectivity test for functions with a finpred domain      *)
(*                                                                    *)
(**********************************************************************)

Section Injectiveb.

Variables (aT rT : eqType) (f : aT -> rT).
Implicit Type D : {finpred aT}.

Definition dinjectiveb (D : finpred aT) := uniq (map f (support D)).

Lemma dinjectivePn D :
  reflect (exists2 x, x \in D & exists2 y, y \in [predD1 D & x] & f x = f y)
          (~~ dinjectiveb D).
Proof.
apply: (iffP idP) => [injf | [x Dx [y Dxy eqfxy]]]; last first.
  move: Dx; rewrite -mem_support => /rot_to[i E defE].
  rewrite /dinjectiveb -(rot_uniq i) -map_rot defE /=; apply/nandP; left.
  rewrite inE /= -mem_support -(mem_rot i) defE inE in Dxy.
  rewrite andb_orr andbC andbN in Dxy.
  by rewrite eqfxy map_f //; case/andP: Dxy.
pose P := [pred x in D | ~~ [disjoint [predD1 D & x] & [pred y | f x == f y]]].
have [noP | /pred0Pn[x /andP[Dx]]] := altP (@pred0P _ P); last first.
  by case/pred0Pn=> y /andP[Dy /eqP-Efxy]; exists x => //; exists y.
rewrite /dinjectiveb map_inj_in_uniq ?support_uniq // in injf => x y Dx Dy Efxy.
apply/esym; apply: contraFeq (noP x) => x'y /=; rewrite -mem_support Dx /=.
by apply/pred0Pn; exists y; rewrite !inE x'y -mem_support Dy Efxy eqxx.
Qed.

Lemma dinjectiveP D : reflect {in D &, injective f} (dinjectiveb D).
Proof.
rewrite -[dinjectiveb D]negbK.
case: dinjectivePn=> [noinjf | injf]; constructor.
  case: noinjf => x Dx [y /andP[neqxy /= Dy] eqfxy] injf.
  by case/eqP: neqxy; apply: injf.
move=> x y Dx Dy /= eqfxy; apply/eqP; apply/idPn=> nxy; case: injf.
by exists x => //; exists y => //=; rewrite inE /= eq_sym nxy.
Qed.

End Injectiveb.

Definition image (T : choiceType) T' f (A : finpred T) : seq T' :=
  map f (enum A).
Notation "[ 'seq' F | x 'in' A ]" := (image (fun x => F) A)
  (at level 0, F at level 99, x binder,
   format "'[hv' [ 'seq'  F '/ '  |  x  'in'  A ] ']'") : seq_scope.
Notation "[ 'seq' F | x ]" :=
  [seq F | x in @predT
    (* kludge for getting the type of x *)
    match _, (fun x => I) with
    | T, f
      => match match f return T -> True with f' => f' end with
         | _ => T
         end
    end]
  (at level 0, F at level 99, x binder, only parsing) : seq_scope.
Notation "[ 'seq' F | x : T ]" := [seq F | x : T in @predT T]
  (at level 0, F at level 99, x name, only printing,
   format "'[hv' [ 'seq'  F '/ '  |  x  :  T ] ']'") : seq_scope.
Notation "[ 'seq' F , x ]" := [seq F | x ]
  (at level 0, F at level 99, x binder, only parsing) : seq_scope.

Section ChoiceImage.

Variable T : choiceType.
Implicit Type A : {finpred T}.

Section ChoiceSizeImage.

Variables (T' : Type) (f : T -> T').

Lemma size_image A : size (image f A) = #|A|.
Proof. by rewrite size_map -cardE. Qed.

End ChoiceSizeImage.

Variables (T' : eqType) (f : T -> T').

Lemma imageP A y : reflect (exists2 x, x \in A & y = f x) (y \in image f A).
Proof.
by apply: (iffP mapP) => [] [x Ax y_fx]; exists x; rewrite // mem_enum in Ax *.
Qed.

Remark iinv_proof A y : y \in image f A -> {x | x \in A & f x = y}.
Proof.
move=> fy; pose b := [predI A & [pred x | f x == y]].
case: (pickP b) => [x /andP[Ax /eqP] | nfy]; first by exists x.
by case/negP: fy => /imageP[x Ax fx_y]; case/andP: (nfy x); rewrite inE fx_y.
Qed.

Definition iinv A y fAy := s2val (@iinv_proof A y fAy).

Lemma f_iinv A y fAy : f (@iinv A y fAy) = y.
Proof. exact: s2valP' (iinv_proof fAy). Qed.

Lemma mem_iinv A y fAy : @iinv A y fAy \in A.
Proof. exact: s2valP (iinv_proof fAy). Qed.

Lemma in_iinv_f A : {in A &, injective f} ->
  forall x fAfx, x \in A -> @iinv A (f x) fAfx = x.
Proof.
by move=> injf x fAfx Ax; apply: injf => //; [apply: mem_iinv | apply: f_iinv].
Qed.

Lemma preim_iinv A B y fAy : preim f B (@iinv A y fAy) = B y.
Proof. by rewrite /= f_iinv. Qed.

Lemma image_f A x : x \in A -> f x \in image f A.
Proof. by move=> Ax; apply/imageP; exists x. Qed.

Lemma image_pred0 : image f pred0 =i pred0.
Proof. by move=> x; rewrite /image /= enum0. Qed.

Section ChoiceInjective.

Hypothesis injf : injective f.

Lemma mem_image A x : (f x \in image f A) = (x \in A).
Proof. by rewrite mem_map ?mem_enum. Qed.

Lemma pre_image A : [preim f of image f A] =i A.
Proof. by move=> x; rewrite inE /= mem_image. Qed.

End ChoiceInjective.

End ChoiceImage.
Arguments imageP {T T' f A y}.

Lemma flatten_imageP (aT : choiceType) (rT : eqType)
                     (A : aT -> seq rT) (P : {finpred aT}) (y : rT) :
  reflect (exists2 x, x \in P & y \in A x) (y \in flatten [seq A x | x in P]).
Proof.
by apply: (iffP flatten_mapP) => [][x Px]; exists x; rewrite ?mem_enum in Px *.
Qed.
Arguments flatten_imageP {aT rT A P y}.

Section ChoiceCardFunImage.

Variables (T : choiceType) (T' : eqType) (f : T -> T').
Implicit Type A : {finpred T}.

Lemma leq_image_card A : #|image f A| <= #|A|.
Proof. by rewrite (cardE A) -(size_map f) card_size. Qed.

Lemma card_in_image A : {in A &, injective f} -> #|image f A| = #|A|.
Proof.
move=> injf; rewrite (cardE A) -(size_map f); apply/card_uniqP.
by rewrite map_inj_in_uniq// => x y; rewrite !mem_enum; apply: injf.
Qed.

Lemma image_injP A : reflect {in A &, injective f} (#|image f A| == #|A|).
Proof.
apply: (iffP eqP); [rewrite [in RHS]unlock=> eqfA | exact: card_in_image].
apply/dinjectiveP/card_uniqP; rewrite size_map -{}eqfA.
by apply/esym/eq_card/eq_mem_map; rewrite unlock; apply: mem_sort.
Qed.

Hypothesis injf : injective f.

Lemma card_image A : #|image f A| = #|A|.
Proof. by apply: card_in_image; apply: in2W. Qed.

End ChoiceCardFunImage.
Arguments image_injP {T T' f A}.

(* Subtype for an explicit enumeration. *)
Section SeqSubType.

Variables (T : eqType) (s : seq T).

Record seq_sub : Type := SeqSub {ssval : T; ssvalP : in_mem ssval (@mem T _ s)}.

HB.instance Definition _ := [isSub for ssval].
HB.instance Definition _ := [Equality of seq_sub by <:].

Definition seq_sub_enum : seq seq_sub := undup (pmap insub s).

Lemma mem_seq_sub_enum x : x \in seq_sub_enum.
Proof. by rewrite mem_undup mem_pmap -valK map_f ?ssvalP. Qed.

Lemma val_seq_sub_enum : uniq s -> map val seq_sub_enum = s.
Proof.
move=> Us; rewrite /seq_sub_enum undup_id ?pmap_sub_uniq //.
rewrite (pmap_filter (insubK _)); apply/all_filterP.
by apply/allP => x; rewrite isSome_insub.
Qed.

Definition seq_sub_pickle x := index x seq_sub_enum.
Definition seq_sub_unpickle n := nth None (map some seq_sub_enum) n.
Lemma seq_sub_pickleK : pcancel seq_sub_pickle seq_sub_unpickle.
Proof.
rewrite /seq_sub_unpickle => x.
by rewrite (nth_map x) ?nth_index ?index_mem ?mem_seq_sub_enum.
Qed.

Definition seq_sub_isCountable := isCountable.Build seq_sub seq_sub_pickleK.

(* Beware: these are not the canonical instances, as they are not consistent  *)
(* with the generic sub_choiceType canonical instance.                        *)
Definition adhoc_seq_sub_choiceType : choiceType := pcan_type seq_sub_pickleK.
Definition adhoc_seq_sub_countType := HB.pack_for countType seq_sub
  seq_sub_isCountable (Choice.class adhoc_seq_sub_choiceType).

End SeqSubType.

Section SeqReplace.
Variables (T : eqType).
Implicit Types (s : seq T).

Lemma seq_sub_default s : size s > 0 -> seq_sub s.
Proof. by case: s => // x s _; exists x; rewrite mem_head. Qed.

Lemma seq_subE s (s_gt0 : size s > 0) :
  s = map val (map (insubd (seq_sub_default s_gt0)) s : seq (seq_sub s)).
Proof. by rewrite -map_comp map_id_in// => x x_in_s /=; rewrite insubdK. Qed.

End SeqReplace.
Notation in_sub_seq s_gt0 := (insubd (seq_sub_default s_gt0)).

Section Extrema.

Variant extremum_spec {T : Type} (ord : rel T) {I : Type}
  (P : pred I) (F : I -> T) : I -> Type :=
  ExtremumSpec (i : I) of P i & (forall j : I, P j -> ord (F i) (F j)) :
                   extremum_spec ord P F i.

Let arg_pred {T : eqType} ord {I : eqType} (P : {finpred I}) (F : I -> T) :=
  [pred i | i \in P & all (fun j => ord (F i) (F j)) (support P)].

Section Extremum.

Context {T : eqType} {I : choiceType} (ord : rel T).
Context (i0 : I) (P : {finpred I}) (F : I -> T).  (* TODO: should it be "finpred I" for the definition of extremum? *)

Definition extremum := odflt i0 (pick (arg_pred ord P F)).

Hypothesis ord_refl : reflexive ord.
Hypothesis ord_trans : transitive ord.
Hypothesis ord_total : total ord.
Hypothesis Pi0 : i0 \in P.

Lemma extremumP : extremum_spec ord [in P] F extremum.
Proof.
rewrite /extremum; case: pickP => [i /andP[Pi /allP min_i] | no_i].
  by split=> //= j Pj; apply: min_i; rewrite mem_support.
have := sort_sorted ord_total [seq F i | i <- enum P].
set s := sort _ _ => ss; have s_gt0 : size s > 0
   by rewrite size_sort size_map -cardE; apply/card_gt0P; exists i0.
pose t0 := nth (F i0) s 0; have: t0 \in s by rewrite mem_nth.
rewrite mem_sort => /mapP/sig2_eqW[it0]; rewrite mem_enum => it0P def_t0.
have /negP[/=] := no_i it0; rewrite inE it0P/=; apply/allP => j /[!inE] Pj.
have /(nthP (F i0))[k g_lt <-] : F j \in s by rewrite mem_sort map_f ?mem_enum.
by rewrite -def_t0 sorted_leq_nth.
Qed.

End Extremum.

Section ExtremumIn.

Context {T : eqType} {I : choiceType} (ord : rel T).
Context (i0 : I) (P : {finpred I}) (F : I -> T).  (* TODO: or finpred I ? *)

Hypothesis ord_refl : {in P, reflexive (relpre F ord)}.
Hypothesis ord_trans : {in P & P & P, transitive (relpre F ord)}.
Hypothesis ord_total : {in P &, total (relpre F ord)}.
Hypothesis Pi0 : i0 \in P.

Lemma extremum_inP : extremum_spec ord [in P] F (extremum ord i0 P F).
Proof.
rewrite /extremum; case: pickP => [i /andP[Pi /allP min_i] | no_i].
  by split=> //= j Pj; apply: min_i; rewrite mem_support.
pose TP := seq_sub [seq F i | i <- enum P].
have FPP (iP : {i | i \in P}) : F (proj1_sig iP) \in [seq F i | i <- enum P].
  by rewrite map_f// mem_enum; apply: valP.
pose FP := SeqSub (FPP _).
have []//= := @extremumP _ _ (relpre val ord) (exist [in P] i0 Pi0)
    [pred x | val x \in P] FP.
- by move=> [/= _/mapP[i iP ->]]; apply: ord_refl; rewrite mem_enum in iP.
- move=> [/= _/mapP[j jP ->]] [/= _/mapP[i iP ->]] [/= _/mapP[k kP ->]].
  by apply: ord_trans; rewrite !mem_enum in iP jP kP.
- move=> [/= _/mapP[i iP ->]] [/= _/mapP[j jP ->]].
  by apply: ord_total; rewrite !mem_enum in iP jP.
- rewrite /FP => -[/= i Pi] _ /(_ (exist _ _ _))/= ordF.
  have/negP/negP/= := no_i i; rewrite inE Pi/= -has_predC => /hasP/sig2W[j].
  by rewrite !inE => Pj; rewrite ordF.
Qed.

End ExtremumIn.

Notation "[ 'arg[' ord ]_( i < i0 | P ) F ]" :=
    (extremum ord i0 [pred i | P%B] (fun i => F))
  (at level 0, ord, i, i0 at level 10,
   format "[ 'arg[' ord ]_( i  <  i0  |  P )  F ]") : nat_scope.

Notation "[ 'arg[' ord ]_( i < i0 'in' A ) F ]" :=
    [arg[ord]_(i < i0 | i \in A) F]
  (at level 0, ord, i, i0 at level 10,
   format "[ 'arg[' ord ]_( i  <  i0  'in'  A )  F ]") : nat_scope.

Notation "[ 'arg[' ord ]_( i < i0 ) F ]" := [arg[ord]_(i < i0 | true) F]
  (at level 0, ord, i, i0 at level 10,
   format "[ 'arg[' ord ]_( i  <  i0 )  F ]") : nat_scope.

Section ArgMinMax.

Variables (I : choiceType) (i0 : I).
Variables (P : {finpred I}) (F : I -> nat) (Pi0 : i0 \in P).

Definition arg_min := extremum leq i0 P F.
Definition arg_max := extremum geq i0 P F.

Lemma arg_minnP : extremum_spec leq [in P] F arg_min.
Proof. by apply: extremumP => //; [apply: leq_trans|apply: leq_total]. Qed.

Lemma arg_maxnP : extremum_spec geq [in P] F arg_max.
Proof.
apply: extremumP => //; first exact: leqnn.
  by move=> n m p mn np; apply: leq_trans mn.
by move=> ??; apply: leq_total.
Qed.

End ArgMinMax.

End Extrema.

Notation "[ 'arg' 'min_' ( i < i0 | P ) F ]" :=
    (arg_min i0 [pred i | P%B] (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0  |  P )  F ]") : nat_scope.

Notation "[ 'arg' 'min_' ( i < i0 'in' A ) F ]" :=
    [arg min_(i < i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0  'in'  A )  F ]") : nat_scope.

Notation "[ 'arg' 'min_' ( i < i0 ) F ]" := [arg min_(i < i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0 )  F ]") : nat_scope.

Notation "[ 'arg' 'max_' ( i > i0 | P ) F ]" :=
     (arg_max i0 [pred i | P%B] (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0  |  P )  F ]") : nat_scope.

Notation "[ 'arg' 'max_' ( i > i0 'in' A ) F ]" :=
    [arg max_(i > i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0  'in'  A )  F ]") : nat_scope.

Notation "[ 'arg' 'max_' ( i > i0 ) F ]" := [arg max_(i > i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0 )  F ]") : nat_scope.
