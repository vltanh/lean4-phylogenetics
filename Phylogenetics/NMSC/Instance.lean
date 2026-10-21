module

public import Phylogenetics.Defs
/-!
# The CF formulas of a metric cycle satisfy the property `NMSCQuartetCF`

The property `Phylogenetics.NMSCQuartetCF Ω ord CF` fixes the CFs of distinct components to the
formulas `Phylogenetics.cycleCF` of the induced metric quarnets; the formulas themselves have it,
so a result stated under the property applies to the formulas of an explicit metric cycle. The
component CFs of a cycle of a network have the property by `Phylogenetics.nmsc_quartetCF`. -/

@[expose] public section

namespace Phylogenetics

variable {d : ℕ}

/-- The component CFs given by the formulas `cycleCF` have the property `NMSCQuartetCF`. -/
theorem nmscQuartetCF_cycleCF (Ω : MetricCycle d) (ord : Equiv.Perm (Fin d)) :
    NMSCQuartetCF Ω ord
      (fun a b c e => cycleCF Ω (ord.symm a) (ord.symm b) (ord.symm c) (ord.symm e)) :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl

end Phylogenetics
