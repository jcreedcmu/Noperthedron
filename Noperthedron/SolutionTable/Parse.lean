import Noperthedron.SolutionTable.Defs


namespace Noperthedron.Solution

/-
27 columns:
ID,nodeType,nrChildren,IDfirstChild,split,
T1_min,T1_max,V1_min,V1_max,T2_min,T2_max,V2_min,V2_max,
A_min,A_max,
P1_index,P2_index,P3_index,
Q1_index,Q2_index,Q3_index,
r,sigma_Q,
wx_nominator,wy_nominator,w_denominator,
S_index
-/

def parseRowCsv (s : String) : Except String Row := Id.run do
  let cols := s.splitOn ","
  let id_str::type_str::nr_children_str::rest := cols | return .error "not enough columns"
  let .some node_id := id_str.toNat? | return .error "failed to parse"
  let .some node_type := type_str.toNat? | return .error "failed to parse"
  let .some nr_children := nr_children_str.toNat? | return .error "failed to parse"
  let id_fst_child_str::split_str::rest := rest | return .error "not enough columns"
  let .some id_fst_child := id_fst_child_str.toNat? | return .error "failed to parse"
  let .some split := split_str.toNat? | return .error "failed to parse"

  let t1min_str::t1max_str::v1min_str::v1max_str::rest := rest | return .error "not enough columns"
  let .some t1min := t1min_str.toInt? | return .error "failed to parse t1min"
  let .some t1max := t1max_str.toInt? | return .error "failed to parse t1max"
  let .some v1min := v1min_str.toInt? | return .error "failed to parse v1min"
  let .some v1max := v1max_str.toInt? | return .error "failed to parse v1max"

  let t2min_str::t2max_str::v2min_str::v2max_str::rest := rest | return .error "not enough columns"
  let .some t2min := t2min_str.toInt? | return .error "failed to parse t2min"
  let .some t2max := t2max_str.toInt? | return .error "failed to parse t2max"
  let .some v2min := v2min_str.toInt? | return .error "failed to parse v2min"
  let .some v2max := v2max_str.toInt? | return .error "failed to parse v2max"

  let amin_str::amax_str::rest := rest | return .error "not enough columns"
  let .some amin := amin_str.toInt? | return .error "failed to parse amin"
  let .some amax := amax_str.toInt? | return .error "failed to parse amax"

  let pmin : Pose ℤ := { θ₁ := t1min, θ₂ := t2min, φ₁ := v1min, φ₂ := v2min, α := amin }
  let pmax : Pose ℤ := { θ₁ := t1max, θ₂ := t2max, φ₁ := v1max, φ₂ := v2max, α := amax }
  let interval ← if h : t1min ≤ t1max ∧ t2min ≤ t2max ∧ v1min ≤ v1max ∧ v2min ≤ v2max ∧
                        amin ≤ amax
                 then Interval.ofIntPose pmin pmax ((Pose.le_iff _ _).mpr h)
                 else return .error "invalid interval"

  let p1i_str::p2i_str::p3i_str::rest := rest | return .error "not enough columns"
  let .some p1i := p1i_str.toNat? | return .error "failed to parse p1i"
  let p1i : Fin 90 ← if h : p1i < 90 then (⟨p1i, h⟩ : Fin 90) else return .error "invalid index"
  let .some p2i := p2i_str.toNat? | return .error "failed to parse p2i"
  let p2i : Fin 90 ← if h : p2i < 90 then (⟨p2i, h⟩ : Fin 90) else return .error "invalid index"
  let .some p3i := p3i_str.toNat? | return .error "failed to parse p3i"
  let p3i : Fin 90 ← if h : p3i < 90 then (⟨p3i, h⟩ : Fin 90) else return .error "invalid index"

  let q1i_str::q2i_str::q3i_str::rest := rest | return .error "not enough columns"
  let .some q1i := q1i_str.toNat? | return .error "failed to parse q1i"
  let q1i : Fin 90 ← if h : q1i < 90 then (⟨q1i, h⟩ : Fin 90) else return .error "invalid index"
  let .some q2i := q2i_str.toNat? | return .error "failed to parse q2i"
  let q2i : Fin 90 ← if h : q2i < 90 then (⟨q2i, h⟩ : Fin 90) else return .error "invalid index"
  let .some q3i := p3i_str.toNat? | return .error "failed to parse q3i"
  let q3i : Fin 90 ← if h : q3i < 90 then (⟨q3i, h⟩ : Fin 90) else return .error "invalid index"

  let r_str :: sigmaq_str :: rest := rest | return .error "not enough columns"
  let .some r' := r_str.toInt? | return .error "failed to parse r'"
  let .some sigmaqN := sigmaq_str.toNat? | return .error "failed to parse sigmaqN"
  let sigmaq : Finset.Icc 0 1 ←
    match sigmaqN with
    | 0 => (⟨0, by grind⟩ : Finset.Icc 0 1)
    | 1 => (⟨1, by grind⟩ : Finset.Icc 0 1)
    | _ => return .error s!"bad sigmaq: {sigmaqN}"

  let wxnum_str::wynum_str::wden_str::rest := rest | return .error "not enough columns"
  let .some wxnum := wxnum_str.toInt? | return .error "failed to parse wxnum"
  let .some wynum := wynum_str.toInt? | return .error "failed to parse wynum"
  let .some wden := wden_str.toNat? | return .error "failed to parse wden"

  let sindex_str :: rest := rest | return .error "not enough columns"
  let .some sindex := sindex_str.toNat? | return .error "failed to parse sindex"
  let sindex : Fin 90 ← if h : sindex < 90 then (⟨sindex, h⟩ : Fin 90)
                        else return .error "invalid sindex"

  let [] := rest | return .error "too many columns"

  return .ok {
    ID := node_id
    nodeType := node_type
    nrChildren := nr_children
    IDfirstChild := id_fst_child
    split := split
    interval := interval
    S_index := VertexIndex.ofFin90 sindex
    wx_numerator := wxnum
    wy_numerator := wynum
    w_denominator := wden
    P1_index := VertexIndex.ofFin90 p1i
    P2_index := VertexIndex.ofFin90 p2i
    P3_index := VertexIndex.ofFin90 p3i
    Q1_index := VertexIndex.ofFin90 q1i
    Q2_index := VertexIndex.ofFin90 q2i
    Q3_index := VertexIndex.ofFin90 q3i
    r' := r'
    sigma_Q := sigmaq
  }

--#eval parseRowCsv "1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,1,24,25,26,27"
