import Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate

open Noperthedron.Nopert229
open Noperthedron.Nopert229.AtlasProjectiveAnnularCertificate
open Noperthedron.Nopert229.AtlasProjectiveLocalCertificate

-- 15 Core Axes Definitions
def coreAxis_0 : AxisCertificate := {
  edgeStart := ![2, 10, 2],
  edgeFinish := ![1, 15, 1],
  edgeStart₂ := ![1, 15, 1],
  edgeFinish₂ := ![4, 19, 4],
  mix := ![0, 666, 800],
  index := ![1, 15, 1],
  nonzeroWitness := ![15, 1, 15],
  B := 38424249/62500000
}

def coreAxis_1 : AxisCertificate := {
  edgeStart := ![2, 10, 2],
  edgeFinish := ![1, 15, 1],
  edgeStart₂ := ![1, 15, 1],
  edgeFinish₂ := ![4, 19, 4],
  mix := ![0, 800, 800],
  index := ![1, 15, 1],
  nonzeroWitness := ![15, 1, 15],
  B := 173713389/250000000
}

def coreAxis_2 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 333, 0],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 10],
  B := 519773829/1000000000
}

def coreAxis_3 : AxisCertificate := {
  edgeStart := ![2, 10, 3],
  edgeFinish := ![1, 15, 2],
  edgeStart₂ := ![1, 15, 2],
  edgeFinish₂ := ![4, 19, 1],
  mix := ![0, 800, 0],
  index := ![1, 15, 2],
  nonzeroWitness := ![15, 1, 10],
  B := 173713389/200000000
}

def coreAxis_4 : AxisCertificate := {
  edgeStart := ![2, 8, 19],
  edgeFinish := ![1, 9, 3],
  edgeStart₂ := ![1, 9, 3],
  edgeFinish₂ := ![4, 10, 2],
  mix := ![0, 666, 666],
  index := ![1, 9, 3],
  nonzeroWitness := ![15, 3, 9],
  B := 1011572653/1000000000
}

def coreAxis_5 : AxisCertificate := {
  edgeStart := ![2, 8, 19],
  edgeFinish := ![1, 9, 3],
  edgeStart₂ := ![1, 9, 3],
  edgeFinish₂ := ![4, 10, 2],
  mix := ![0, 800, 800],
  index := ![1, 9, 3],
  nonzeroWitness := ![15, 3, 9],
  B := 195319419/200000000
}

def coreAxis_6 : AxisCertificate := {
  edgeStart := ![2, 4, 19],
  edgeFinish := ![1, 8, 3],
  edgeStart₂ := ![1, 8, 3],
  edgeFinish₂ := ![4, 9, 2],
  mix := ![0, 200, 1000],
  index := ![1, 8, 3],
  nonzeroWitness := ![15, 3, 8],
  B := 896947911/1000000000
}

def coreAxis_7 : AxisCertificate := {
  edgeStart := ![2, 4, 19],
  edgeFinish := ![1, 8, 3],
  edgeStart₂ := ![1, 8, 3],
  edgeFinish₂ := ![4, 9, 2],
  mix := ![0, 333, 1000],
  index := ![1, 8, 3],
  nonzeroWitness := ![15, 3, 8],
  B := 433647101/500000000
}

def coreAxis_8 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![0, 0, 0],
  index := ![1, 4, 15],
  nonzeroWitness := ![15, 19, 4],
  B := 146946893/200000000
}

def coreAxis_9 : AxisCertificate := {
  edgeStart := ![2, 1, 15],
  edgeFinish := ![1, 4, 19],
  edgeStart₂ := ![1, 4, 19],
  edgeFinish₂ := ![4, 8, 3],
  mix := ![0, 0, 500],
  index := ![1, 4, 19],
  nonzeroWitness := ![15, 19, 4],
  B := 726518289/1000000000
}

def coreAxis_10 : AxisCertificate := {
  edgeStart := ![2, 1, 15],
  edgeFinish := ![1, 4, 19],
  edgeStart₂ := ![1, 4, 19],
  edgeFinish₂ := ![4, 8, 3],
  mix := ![0, 0, 666],
  index := ![1, 4, 19],
  nonzeroWitness := ![15, 19, 4],
  B := 729246059/1000000000
}

def coreAxis_11 : AxisCertificate := {
  edgeStart := ![2, 1, 15],
  edgeFinish := ![1, 4, 19],
  edgeStart₂ := ![1, 4, 19],
  edgeFinish₂ := ![4, 8, 3],
  mix := ![0, 200, 800],
  index := ![1, 4, 19],
  nonzeroWitness := ![15, 19, 4],
  B := 146296799/250000000
}

def coreAxis_12 : AxisCertificate := {
  edgeStart := ![2, 1, 15],
  edgeFinish := ![1, 4, 19],
  edgeStart₂ := ![1, 4, 19],
  edgeFinish₂ := ![4, 8, 3],
  mix := ![0, 333, 1000],
  index := ![1, 4, 19],
  nonzeroWitness := ![15, 19, 4],
  B := 245064413/500000000
}

def coreAxis_13 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![0, 800, 200],
  index := ![1, 4, 15],
  nonzeroWitness := ![15, 15, 4],
  B := 140539527/1000000000
}

def coreAxis_14 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![200, 800, 200],
  index := ![1, 4, 15],
  nonzeroWitness := ![15, 15, 4],
  B := 209116899/1000000000
}

def coreAxis_15 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![333, 800, 200],
  index := ![1, 4, 15],
  nonzeroWitness := ![15, 15, 4],
  B := 254720851/1000000000
}

def coreAxis_16 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![500, 800, 200],
  index := ![1, 4, 15],
  nonzeroWitness := ![15, 15, 4],
  B := 311982957/1000000000
}

def coreAxis_17 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![666, 800, 200],
  index := ![1, 4, 15],
  nonzeroWitness := ![15, 15, 4],
  B := 184456321/500000000
}

def coreAxis_18 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![800, 1000, 333],
  index := ![1, 4, 15],
  nonzeroWitness := ![15, 15, 1],
  B := 415819063/1000000000
}

def coreAxis_19 : AxisCertificate := {
  edgeStart := ![2, 1, 10],
  edgeFinish := ![1, 4, 15],
  edgeStart₂ := ![1, 4, 15],
  edgeFinish₂ := ![4, 8, 19],
  mix := ![1000, 1000, 333],
  index := ![1, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 519773829/1000000000
}

def coreAxis_20 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 500, 800],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 977483567/1000000000
}

def coreAxis_21 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 800, 200],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 4],
  B := 483471289/1000000000
}

def coreAxis_22 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 800, 333],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 578456463/1000000000
}

def coreAxis_23 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 800, 666],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 408194489/500000000
}

def coreAxis_24 : AxisCertificate := {
  edgeStart := ![3, 1, 10],
  edgeFinish := ![2, 4, 15],
  edgeStart₂ := ![2, 4, 15],
  edgeFinish₂ := ![1, 8, 19],
  mix := ![0, 1000, 333],
  index := ![2, 4, 15],
  nonzeroWitness := ![10, 15, 1],
  B := 519773829/1000000000
}

def coreAxes (m : Fin 15) : AxisCertificate :=
  match m.val with
  | 0 => coreAxis_0
  | 1 => coreAxis_1
  | 2 => coreAxis_2
  | 3 => coreAxis_3
  | 4 => coreAxis_4
  | 5 => coreAxis_5
  | 6 => coreAxis_6
  | 7 => coreAxis_7
  | 8 => coreAxis_8
  | 9 => coreAxis_9
  | 10 => coreAxis_10
  | 11 => coreAxis_11
  | 12 => coreAxis_12
  | 13 => coreAxis_13
  | 14 => coreAxis_14
  | 15 => coreAxis_15
  | 16 => coreAxis_16
  | 17 => coreAxis_17
  | 18 => coreAxis_18
  | 19 => coreAxis_19
  | 20 => coreAxis_20
  | 21 => coreAxis_21
  | 22 => coreAxis_22
  | 23 => coreAxis_23
  | 24 => coreAxis_24
  | _ => coreAxis_0

