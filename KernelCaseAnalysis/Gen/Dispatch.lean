module

public import Noperthedron.SolutionTable.Assemble
public meta import Noperthedron.SolutionTable.Load
public import KernelCaseAnalysis.Gen.Load000
public import KernelCaseAnalysis.Gen.Load001
public import KernelCaseAnalysis.Gen.Load002
public import KernelCaseAnalysis.Gen.Load003
public import KernelCaseAnalysis.Gen.Load004
public import KernelCaseAnalysis.Gen.Load005
public import KernelCaseAnalysis.Gen.Load006
public import KernelCaseAnalysis.Gen.Load007
public import KernelCaseAnalysis.Gen.Load008
public import KernelCaseAnalysis.Gen.Load009
public import KernelCaseAnalysis.Gen.Load010
public import KernelCaseAnalysis.Gen.Load011
public import KernelCaseAnalysis.Gen.Load012
public import KernelCaseAnalysis.Gen.Load013
public import KernelCaseAnalysis.Gen.Load014
public import KernelCaseAnalysis.Gen.Load015
public import KernelCaseAnalysis.Gen.Load016
public import KernelCaseAnalysis.Gen.Load017
public import KernelCaseAnalysis.Gen.Load018
public import KernelCaseAnalysis.Gen.Load019
public import KernelCaseAnalysis.Gen.Load020
public import KernelCaseAnalysis.Gen.Load021
public import KernelCaseAnalysis.Gen.Load022
public import KernelCaseAnalysis.Gen.Load023
public import KernelCaseAnalysis.Gen.Load024
public import KernelCaseAnalysis.Gen.Load025
public import KernelCaseAnalysis.Gen.Load026
public import KernelCaseAnalysis.Gen.Load027
public import KernelCaseAnalysis.Gen.Load028
public import KernelCaseAnalysis.Gen.Load029
public import KernelCaseAnalysis.Gen.Load030
public import KernelCaseAnalysis.Gen.Load031
public import KernelCaseAnalysis.Gen.Load032
public import KernelCaseAnalysis.Gen.Load033
public import KernelCaseAnalysis.Gen.Load034
public import KernelCaseAnalysis.Gen.Load035
public import KernelCaseAnalysis.Gen.Load036
public import KernelCaseAnalysis.Gen.Load037
public import KernelCaseAnalysis.Gen.Load038
public import KernelCaseAnalysis.Gen.Load039
public import KernelCaseAnalysis.Gen.Load040
public import KernelCaseAnalysis.Gen.Load041
public import KernelCaseAnalysis.Gen.Load042
public import KernelCaseAnalysis.Gen.Load043
public import KernelCaseAnalysis.Gen.Load044
public import KernelCaseAnalysis.Gen.Load045
public import KernelCaseAnalysis.Gen.Load046
public import KernelCaseAnalysis.Gen.Load047
public import KernelCaseAnalysis.Gen.Load048
public import KernelCaseAnalysis.Gen.Load049
public import KernelCaseAnalysis.Gen.Load050
public import KernelCaseAnalysis.Gen.Load051
public import KernelCaseAnalysis.Gen.Load052
public import KernelCaseAnalysis.Gen.Load053
public import KernelCaseAnalysis.Gen.Load054
public import KernelCaseAnalysis.Gen.Load055
public import KernelCaseAnalysis.Gen.Load056
public import KernelCaseAnalysis.Gen.Load057
public import KernelCaseAnalysis.Gen.Load058
public import KernelCaseAnalysis.Gen.Load059
public import KernelCaseAnalysis.Gen.Load060
public import KernelCaseAnalysis.Gen.Load061
public import KernelCaseAnalysis.Gen.Load062

/-! GENERATED (scripts/gen_kernel_chunks.py): the digit-curried dispatch over
all 4007 loaded chunks and the row getter for the kernel run. -/

@[expose] public section

namespace Noperthedron.Solution

assemble_row_dispatch_curried tableDispatch rows 2051521 chunkSize 512

/-- The full-table row getter: seven `Fin 8` digit levels per access
(`O(log)`), no `List` walk. -/
noncomputable def getRow : ℕ → Row := rowGetterC tableDispatch

end Noperthedron.Solution

end
