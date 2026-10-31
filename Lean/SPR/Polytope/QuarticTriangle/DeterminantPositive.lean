import SPR.Polytope.QuarticTriangle.ConeSubdivision

/-! # Static exact determinant certificate. Each named subdivision identity is checked
by ring; the covering lemma handles all boundaries. Leaf signs are checked by positivity.
The Python authoring script is not used by Lean, Lake, or the axiom audit. -/
namespace SPR.Polytope.QuarticTriangle
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def form_0000000 (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (799551 / 128 : ℝ)*u^2*v^1 + (996795 / 128 : ℝ)*u^2*w^1 + (1643409 / 256 : ℝ)*u^1*v^2 + (264415653 / 16384 : ℝ)*u^1*v^1*w^1 + (21703191 / 4096 : ℝ)*u^1*w^2 + (1152411543 / 524288 : ℝ)*v^3 + (17513238159 / 2097152 : ℝ)*v^2*w^1 + (2990567325 / 524288 : ℝ)*v^1*w^2 + (2115722257 / 2097152 : ℝ)*w^3

private theorem form_0000000_pos : ConePositive form_0000000 := by
  intro u v w hu hv hw hs
  unfold form_0000000
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0000001 (u v w : ℝ) : ℝ :=
  (1152411543 / 524288 : ℝ)*u^3 + (1774383813 / 262144 : ℝ)*u^2*v^1 + (17879370147 / 2097152 : ℝ)*u^2*w^1 + (910273221 / 131072 : ℝ)*u^1*v^2 + (9236587779 / 524288 : ℝ)*u^1*v^1*w^1 + (6573355539 / 1048576 : ℝ)*u^1*w^2 + (155590551 / 65536 : ℝ)*v^3 + (4766589027 / 524288 : ℝ)*v^2*w^1 + (3498961395 / 524288 : ℝ)*v^1*w^2 + (185339503 / 131072 : ℝ)*w^3

private theorem form_0000001_pos : ConePositive form_0000001 := by
  intro u v w hu hv hw hs
  unfold form_0000001
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00000020 (u v w : ℝ) : ℝ :=
  (2115722257 / 2097152 : ℝ)*u^3 + (6772284525 / 2097152 : ℝ)*u^2*v^1 + (7929466521 / 4194304 : ℝ)*u^2*w^1 + (28789132971 / 8388608 : ℝ)*u^1*v^2 + (8909263527 / 2097152 : ℝ)*u^1*v^1*w^1 + (6783787467 / 8388608 : ℝ)*u^1*w^2 + (10162859113 / 8388608 : ℝ)*v^3 + (39551495937 / 16777216 : ℝ)*v^2*w^1 + (9016332309 / 8388608 : ℝ)*v^1*w^2 + (1863931851 / 16777216 : ℝ)*w^3

private theorem form_00000020_pos : ConePositive form_00000020 := by
  intro u v w hu hv hw hs
  unfold form_00000020
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00000021 (u v w : ℝ) : ℝ :=
  (10162859113 / 8388608 : ℝ)*u^3 + (32188021707 / 8388608 : ℝ)*u^2*v^1 + (42950384673 / 16777216 : ℝ)*u^2*w^1 + (8471728893 / 2097152 : ℝ)*u^1*v^2 + (5857965687 / 1048576 : ℝ)*u^1*v^1*w^1 + (12930223635 / 8388608 : ℝ)*u^1*w^2 + (185339503 / 131072 : ℝ)*v^3 + (3173260713 / 1048576 : ℝ)*v^2*w^1 + (3789486981 / 2097152 : ℝ)*v^1*w^2 + (790528221 / 2097152 : ℝ)*w^3

private theorem form_00000021_pos : ConePositive form_00000021 := by
  intro u v w hu hv hw hs
  unfold form_00000021
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000000220 (u v w : ℝ) : ℝ :=
  (1863931851 / 16777216 : ℝ)*u^3 + (7824340395 / 16777216 : ℝ)*u^2*v^1 + (3207811725 / 33554432 : ℝ)*u^2*w^1 + (40222794753 / 67108864 : ℝ)*u^1*v^2 + (7945852239 / 16777216 : ℝ)*u^1*v^1*w^1 + (638576457 / 67108864 : ℝ)*u^1*w^2 + (16381135791 / 67108864 : ℝ)*v^3 + (50722284717 / 134217728 : ℝ)*v^2*w^1 + (10674386979 / 67108864 : ℝ)*v^1*w^2 + (6445805767 / 134217728 : ℝ)*w^3

private theorem form_000000220_pos : ConePositive form_000000220 := by
  intro u v w hu hv hw hs
  unfold form_000000220
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000000221 (u v w : ℝ) : ℝ :=
  (16381135791 / 67108864 : ℝ)*u^3 + (58064019993 / 67108864 : ℝ)*u^2*v^1 + (68563509957 / 134217728 : ℝ)*u^2*w^1 + (16744953015 / 16777216 : ℝ)*u^1*v^2 + (21873186153 / 16777216 : ℝ)*u^1*v^1*w^1 + (29608442187 / 67108864 : ℝ)*u^1*w^2 + (790528221 / 2097152 : ℝ)*v^3 + (51957297 / 65536 : ℝ)*v^2*w^1 + (4953861507 / 8388608 : ℝ)*v^1*w^2 + (414126421 / 2097152 : ℝ)*w^3

private theorem form_000000221_pos : ConePositive form_000000221 := by
  intro u v w hu hv hw hs
  unfold form_000000221
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000000222 (u v w : ℝ) : ℝ :=
  (6445805767 / 134217728 : ℝ)*u^3 + (39409038345 / 134217728 : ℝ)*u^2*v^1 + (4674710211 / 16777216 : ℝ)*u^2*w^1 + (29733686547 / 67108864 : ℝ)*u^1*v^2 + (7323595215 / 8388608 : ℝ)*u^1*v^1*w^1 + (1329254757 / 2097152 : ℝ)*u^1*w^2 + (414126421 / 2097152 : ℝ)*v^3 + (4985172597 / 8388608 : ℝ)*v^2*w^1 + (1678289049 / 2097152 : ℝ)*v^1*w^2 + (111736081 / 262144 : ℝ)*w^3

private theorem form_000000222_pos : ConePositive form_000000222 := by
  intro u v w hu hv hw hs
  unfold form_000000222
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000000223 (u v w : ℝ) : ℝ :=
  (6445805767 / 134217728 : ℝ)*u^3 + (10674386979 / 67108864 : ℝ)*u^2*v^1 + (39409038345 / 134217728 : ℝ)*u^2*w^1 + (50722284717 / 134217728 : ℝ)*u^1*v^2 + (40287649719 / 67108864 : ℝ)*u^1*v^1*w^1 + (29733686547 / 67108864 : ℝ)*u^1*w^2 + (16381135791 / 67108864 : ℝ)*v^3 + (68563509957 / 134217728 : ℝ)*v^2*w^1 + (29608442187 / 67108864 : ℝ)*v^1*w^2 + (414126421 / 2097152 : ℝ)*w^3

private theorem form_000000223_pos : ConePositive form_000000223 := by
  intro u v w hu hv hw hs
  unfold form_000000223
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00000022 (u v w : ℝ) : ℝ :=
  (1863931851 / 16777216 : ℝ)*u^3 + (10056885237 / 16777216 : ℝ)*u^2*v^1 + (-595995957 / 4194304 : ℝ)*u^2*w^1 + (7258614363 / 8388608 : ℝ)*u^1*v^2 + (656751879 / 2097152 : ℝ)*u^1*v^1*w^1 + (-11578215 / 1048576 : ℝ)*u^1*w^2 + (790528221 / 2097152 : ℝ)*v^3 + (953682345 / 2097152 : ℝ)*v^2*w^1 + (337456077 / 1048576 : ℝ)*v^1*w^2 + (111736081 / 262144 : ℝ)*w^3

private theorem form_00000022_pos : ConePositive form_00000022 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00000022 (u+v/2+w/2) (v/2) (w/2)) = form_000000220 := by
      funext u v w; dsimp [form_00000022, form_000000220]; ring
    rw [he]
    exact form_000000220_pos
  · have he : (fun u v w : ℝ => form_00000022 (u/2) (u/2+v+w/2) (w/2)) = form_000000221 := by
      funext u v w; dsimp [form_00000022, form_000000221]; ring
    rw [he]
    exact form_000000221_pos
  · have he : (fun u v w : ℝ => form_00000022 (u/2) (v/2) (u/2+v/2+w)) = form_000000222 := by
      funext u v w; dsimp [form_00000022, form_000000222]; ring
    rw [he]
    exact form_000000222_pos
  · have he : (fun u v w : ℝ => form_00000022 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_000000223 := by
      funext u v w; dsimp [form_00000022, form_000000223]; ring
    rw [he]
    exact form_000000223_pos

private def form_00000023 (u v w : ℝ) : ℝ :=
  (1863931851 / 16777216 : ℝ)*u^3 + (9016332309 / 8388608 : ℝ)*u^2*v^1 + (10056885237 / 16777216 : ℝ)*u^2*w^1 + (39551495937 / 16777216 : ℝ)*u^1*v^2 + (21947106447 / 8388608 : ℝ)*u^1*v^1*w^1 + (7258614363 / 8388608 : ℝ)*u^1*w^2 + (10162859113 / 8388608 : ℝ)*v^3 + (42950384673 / 16777216 : ℝ)*v^2*w^1 + (12930223635 / 8388608 : ℝ)*v^1*w^2 + (790528221 / 2097152 : ℝ)*w^3

private theorem form_00000023_pos : ConePositive form_00000023 := by
  intro u v w hu hv hw hs
  unfold form_00000023
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0000002 (u v w : ℝ) : ℝ :=
  (2115722257 / 2097152 : ℝ)*u^3 + (7197402279 / 2097152 : ℝ)*u^2*v^1 + (791149875 / 1048576 : ℝ)*u^2*w^1 + (4023580821 / 1048576 : ℝ)*u^1*v^2 + (1345829127 / 524288 : ℝ)*u^1*v^1*w^1 + (-681994701 / 524288 : ℝ)*u^1*w^2 + (185339503 / 131072 : ℝ)*v^3 + (949186677 / 524288 : ℝ)*v^2*w^1 + (-332960409 / 524288 : ℝ)*v^1*w^2 + (111736081 / 262144 : ℝ)*w^3

private theorem form_0000002_pos : ConePositive form_0000002 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0000002 (u+v/2+w/2) (v/2) (w/2)) = form_00000020 := by
      funext u v w; dsimp [form_0000002, form_00000020]; ring
    rw [he]
    exact form_00000020_pos
  · have he : (fun u v w : ℝ => form_0000002 (u/2) (u/2+v+w/2) (w/2)) = form_00000021 := by
      funext u v w; dsimp [form_0000002, form_00000021]; ring
    rw [he]
    exact form_00000021_pos
  · have he : (fun u v w : ℝ => form_0000002 (u/2) (v/2) (u/2+v/2+w)) = form_00000022 := by
      funext u v w; dsimp [form_0000002, form_00000022]; ring
    rw [he]
    exact form_00000022_pos
  · have he : (fun u v w : ℝ => form_0000002 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00000023 := by
      funext u v w; dsimp [form_0000002, form_00000023]; ring
    rw [he]
    exact form_00000023_pos

private def form_0000003 (u v w : ℝ) : ℝ :=
  (2115722257 / 2097152 : ℝ)*u^3 + (2990567325 / 524288 : ℝ)*u^2*v^1 + (7197402279 / 2097152 : ℝ)*u^2*w^1 + (17513238159 / 2097152 : ℝ)*u^1*v^2 + (12552905667 / 1048576 : ℝ)*u^1*v^1*w^1 + (4023580821 / 1048576 : ℝ)*u^1*w^2 + (1152411543 / 524288 : ℝ)*v^3 + (17879370147 / 2097152 : ℝ)*v^2*w^1 + (6573355539 / 1048576 : ℝ)*v^1*w^2 + (185339503 / 131072 : ℝ)*w^3

private theorem form_0000003_pos : ConePositive form_0000003 := by
  intro u v w hu hv hw hs
  unfold form_0000003
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000000 (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (410751 / 64 : ℝ)*u^2*v^1 + (607995 / 64 : ℝ)*u^2*w^1 + (433107 / 64 : ℝ)*u^1*v^2 + (84249765 / 4096 : ℝ)*u^1*v^1*w^1 + (-3973449 / 1024 : ℝ)*u^1*w^2 + (155590551 / 65536 : ℝ)*v^3 + (2899502415 / 262144 : ℝ)*v^2*w^1 + (-167042163 / 65536 : ℝ)*v^1*w^2 + (111736081 / 262144 : ℝ)*w^3

private theorem form_000000_pos : ConePositive form_000000 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_000000 (u+v/2+w/2) (v/2) (w/2)) = form_0000000 := by
      funext u v w; dsimp [form_000000, form_0000000]; ring
    rw [he]
    exact form_0000000_pos
  · have he : (fun u v w : ℝ => form_000000 (u/2) (u/2+v+w/2) (w/2)) = form_0000001 := by
      funext u v w; dsimp [form_000000, form_0000001]; ring
    rw [he]
    exact form_0000001_pos
  · have he : (fun u v w : ℝ => form_000000 (u/2) (v/2) (u/2+v/2+w)) = form_0000002 := by
      funext u v w; dsimp [form_000000, form_0000002]; ring
    rw [he]
    exact form_0000002_pos
  · have he : (fun u v w : ℝ => form_000000 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0000003 := by
      funext u v w; dsimp [form_000000, form_0000003]; ring
    rw [he]
    exact form_0000003_pos

private def form_0000010 (u v w : ℝ) : ℝ :=
  (155590551 / 65536 : ℝ)*u^3 + (956813391 / 131072 : ℝ)*u^2*v^1 + (4859669367 / 524288 : ℝ)*u^2*w^1 + (1960544493 / 262144 : ℝ)*u^1*v^2 + (10017439173 / 524288 : ℝ)*u^1*v^1*w^1 + (59317293 / 8192 : ℝ)*u^1*w^2 + (1338547437 / 524288 : ℝ)*v^3 + (20630305647 / 2097152 : ℝ)*v^2*w^1 + (31314381 / 4096 : ℝ)*v^1*w^2 + (3813892117 / 2097152 : ℝ)*w^3

private theorem form_0000010_pos : ConePositive form_0000010 := by
  intro u v w hu hv hw hs
  unfold form_0000010
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0000011 (u v w : ℝ) : ℝ :=
  (1338547437 / 524288 : ℝ)*u^3 + (1027548909 / 131072 : ℝ)*u^2*v^1 + (21008518947 / 2097152 : ℝ)*u^2*w^1 + (262841679 / 32768 : ℝ)*u^1*v^2 + (5401704465 / 262144 : ℝ)*u^1*v^1*w^1 + (8613344643 / 1048576 : ℝ)*u^1*w^2 + (22403223 / 8192 : ℝ)*v^3 + (1387762155 / 131072 : ℝ)*v^2*w^1 + (2259091185 / 262144 : ℝ)*v^1*w^2 + (582600629 / 262144 : ℝ)*w^3

private theorem form_0000011_pos : ConePositive form_0000011 := by
  intro u v w hu hv hw hs
  unfold form_0000011
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0000012 (u v w : ℝ) : ℝ :=
  (3813892117 / 2097152 : ℝ)*u^3 + (12289412415 / 2097152 : ℝ)*u^2*v^1 + (3849062847 / 1048576 : ℝ)*u^2*w^1 + (6568187451 / 1048576 : ℝ)*u^1*v^2 + (549837309 / 65536 : ℝ)*u^1*v^1*w^1 + (558059355 / 262144 : ℝ)*u^1*w^2 + (582600629 / 262144 : ℝ)*v^3 + (1236512589 / 262144 : ℝ)*v^2*w^1 + (365183559 / 131072 : ℝ)*v^1*w^2 + (28661611 / 16384 : ℝ)*w^3

private theorem form_0000012_pos : ConePositive form_0000012 := by
  intro u v w hu hv hw hs
  unfold form_0000012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0000013 (u v w : ℝ) : ℝ :=
  (3813892117 / 2097152 : ℝ)*u^3 + (31314381 / 4096 : ℝ)*u^2*v^1 + (12289412415 / 2097152 : ℝ)*u^2*w^1 + (20630305647 / 2097152 : ℝ)*u^1*v^2 + (16628390373 / 1048576 : ℝ)*u^1*v^1*w^1 + (6568187451 / 1048576 : ℝ)*u^1*w^2 + (1338547437 / 524288 : ℝ)*v^3 + (21008518947 / 2097152 : ℝ)*v^2*w^1 + (8613344643 / 1048576 : ℝ)*v^1*w^2 + (582600629 / 262144 : ℝ)*w^3

private theorem form_0000013_pos : ConePositive form_0000013 := by
  intro u v w hu hv hw hs
  unfold form_0000013
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000001 (u v w : ℝ) : ℝ :=
  (155590551 / 65536 : ℝ)*u^3 + (245020869 / 32768 : ℝ)*u^2*v^1 + (2992582755 / 262144 : ℝ)*u^2*w^1 + (128422341 / 16384 : ℝ)*u^1*v^2 + (1598801427 / 65536 : ℝ)*u^1*v^1*w^1 + (-129819309 / 131072 : ℝ)*u^1*w^2 + (22403223 / 8192 : ℝ)*v^3 + (850084803 / 65536 : ℝ)*v^2*w^1 + (21244227 / 65536 : ℝ)*v^1*w^2 + (28661611 / 16384 : ℝ)*w^3

private theorem form_000001_pos : ConePositive form_000001 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_000001 (u+v/2+w/2) (v/2) (w/2)) = form_0000010 := by
      funext u v w; dsimp [form_000001, form_0000010]; ring
    rw [he]
    exact form_0000010_pos
  · have he : (fun u v w : ℝ => form_000001 (u/2) (u/2+v+w/2) (w/2)) = form_0000011 := by
      funext u v w; dsimp [form_000001, form_0000011]; ring
    rw [he]
    exact form_0000011_pos
  · have he : (fun u v w : ℝ => form_000001 (u/2) (v/2) (u/2+v/2+w)) = form_0000012 := by
      funext u v w; dsimp [form_000001, form_0000012]; ring
    rw [he]
    exact form_0000012_pos
  · have he : (fun u v w : ℝ => form_000001 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0000013 := by
      funext u v w; dsimp [form_000001, form_0000013]; ring
    rw [he]
    exact form_0000013_pos

private def form_000002 (u v w : ℝ) : ℝ :=
  (111736081 / 262144 : ℝ)*u^3 + (684242535 / 262144 : ℝ)*u^2*v^1 + (843809715 / 131072 : ℝ)*u^2*w^1 + (515570901 / 131072 : ℝ)*u^1*v^2 + (1090021527 / 65536 : ℝ)*u^1*v^1*w^1 + (1974998067 / 65536 : ℝ)*u^1*w^2 + (28661611 / 16384 : ℝ)*v^3 + (666634437 / 65536 : ℝ)*v^2*w^1 + (2140865223 / 65536 : ℝ)*v^1*w^2 + (1176569233 / 32768 : ℝ)*w^3

private theorem form_000002_pos : ConePositive form_000002 := by
  intro u v w hu hv hw hs
  unfold form_000002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00000300 (u v w : ℝ) : ℝ :=
  (111736081 / 262144 : ℝ)*u^3 + (337456077 / 1048576 : ℝ)*u^2*v^1 + (1650261 / 1024 : ℝ)*u^2*w^1 + (953682345 / 2097152 : ℝ)*u^1*v^2 + (2600437119 / 2097152 : ℝ)*u^1*v^1*w^1 + (8153471199 / 4194304 : ℝ)*u^1*w^2 + (790528221 / 2097152 : ℝ)*v^3 + (6042453669 / 8388608 : ℝ)*v^2*w^1 + (15399304809 / 16777216 : ℝ)*v^1*w^2 + (1590883523 / 2097152 : ℝ)*w^3

private theorem form_00000300_pos : ConePositive form_00000300 := by
  intro u v w hu hv hw hs
  unfold form_00000300
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00000301 (u v w : ℝ) : ℝ :=
  (790528221 / 2097152 : ℝ)*u^3 + (3789486981 / 2097152 : ℝ)*u^2*v^1 + (11714062941 / 8388608 : ℝ)*u^2*w^1 + (3173260713 / 1048576 : ℝ)*u^1*v^2 + (133688835 / 32768 : ℝ)*u^1*v^1*w^1 + (27878679549 / 16777216 : ℝ)*u^1*w^2 + (185339503 / 131072 : ℝ)*v^3 + (6771088677 / 2097152 : ℝ)*v^2*w^1 + (19065768975 / 8388608 : ℝ)*v^1*w^2 + (10774729863 / 16777216 : ℝ)*w^3

private theorem form_00000301_pos : ConePositive form_00000301 := by
  intro u v w hu hv hw hs
  unfold form_00000301
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00000302 (u v w : ℝ) : ℝ :=
  (1590883523 / 2097152 : ℝ)*u^3 + (20966624565 / 16777216 : ℝ)*u^2*v^1 + (10937131077 / 4194304 : ℝ)*u^2*w^1 + (5517832797 / 4194304 : ℝ)*u^1*v^2 + (12977746041 / 4194304 : ℝ)*u^1*v^1*w^1 + (3081697203 / 1048576 : ℝ)*u^1*w^2 + (10774729863 / 16777216 : ℝ)*v^3 + (6629210307 / 4194304 : ℝ)*v^2*w^1 + (7734828993 / 4194304 : ℝ)*v^1*w^2 + (1142853097 / 1048576 : ℝ)*w^3

private theorem form_00000302_pos : ConePositive form_00000302 := by
  intro u v w hu hv hw hs
  unfold form_00000302
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00000303 (u v w : ℝ) : ℝ :=
  (1590883523 / 2097152 : ℝ)*u^3 + (15399304809 / 16777216 : ℝ)*u^2*v^1 + (20966624565 / 16777216 : ℝ)*u^2*w^1 + (6042453669 / 8388608 : ℝ)*u^1*v^2 + (17082463671 / 8388608 : ℝ)*u^1*v^1*w^1 + (5517832797 / 4194304 : ℝ)*u^1*w^2 + (790528221 / 2097152 : ℝ)*v^3 + (11714062941 / 8388608 : ℝ)*v^2*w^1 + (27878679549 / 16777216 : ℝ)*v^1*w^2 + (10774729863 / 16777216 : ℝ)*w^3

private theorem form_00000303_pos : ConePositive form_00000303 := by
  intro u v w hu hv hw hs
  unfold form_00000303
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0000030 (u v w : ℝ) : ℝ :=
  (111736081 / 262144 : ℝ)*u^3 + (-332960409 / 524288 : ℝ)*u^2*v^1 + (509725389 / 262144 : ℝ)*u^2*w^1 + (949186677 / 524288 : ℝ)*u^1*v^2 + (-113376591 / 524288 : ℝ)*u^1*v^1*w^1 + (2734835115 / 1048576 : ℝ)*u^1*w^2 + (185339503 / 131072 : ℝ)*v^3 + (2322940605 / 1048576 : ℝ)*v^2*w^1 + (877710411 / 2097152 : ℝ)*v^1*w^2 + (1142853097 / 1048576 : ℝ)*w^3

private theorem form_0000030_pos : ConePositive form_0000030 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0000030 (u+v/2+w/2) (v/2) (w/2)) = form_00000300 := by
      funext u v w; dsimp [form_0000030, form_00000300]; ring
    rw [he]
    exact form_00000300_pos
  · have he : (fun u v w : ℝ => form_0000030 (u/2) (u/2+v+w/2) (w/2)) = form_00000301 := by
      funext u v w; dsimp [form_0000030, form_00000301]; ring
    rw [he]
    exact form_00000301_pos
  · have he : (fun u v w : ℝ => form_0000030 (u/2) (v/2) (u/2+v/2+w)) = form_00000302 := by
      funext u v w; dsimp [form_0000030, form_00000302]; ring
    rw [he]
    exact form_00000302_pos
  · have he : (fun u v w : ℝ => form_0000030 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00000303 := by
      funext u v w; dsimp [form_0000030, form_00000303]; ring
    rw [he]
    exact form_00000303_pos

private def form_0000031 (u v w : ℝ) : ℝ :=
  (185339503 / 131072 : ℝ)*u^3 + (3498961395 / 524288 : ℝ)*u^2*v^1 + (4872715323 / 1048576 : ℝ)*u^2*w^1 + (4766589027 / 524288 : ℝ)*u^1*v^2 + (7294513065 / 524288 : ℝ)*u^1*v^1*w^1 + (10593940287 / 2097152 : ℝ)*u^1*w^2 + (155590551 / 65536 : ℝ)*v^3 + (4859669367 / 524288 : ℝ)*v^2*w^1 + (59317293 / 8192 : ℝ)*v^1*w^2 + (3813892117 / 2097152 : ℝ)*w^3

private theorem form_0000031_pos : ConePositive form_0000031 := by
  intro u v w hu hv hw hs
  unfold form_0000031
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0000032 (u v w : ℝ) : ℝ :=
  (1142853097 / 1048576 : ℝ)*u^3 + (2265158763 / 2097152 : ℝ)*u^2*v^1 + (4122283467 / 1048576 : ℝ)*u^2*w^1 + (3425194815 / 1048576 : ℝ)*u^1*v^2 + (1682601795 / 524288 : ℝ)*u^1*v^1*w^1 + (1203449565 / 262144 : ℝ)*u^1*w^2 + (3813892117 / 2097152 : ℝ)*v^3 + (3849062847 / 1048576 : ℝ)*v^2*w^1 + (558059355 / 262144 : ℝ)*v^1*w^2 + (28661611 / 16384 : ℝ)*w^3

private theorem form_0000032_pos : ConePositive form_0000032 := by
  intro u v w hu hv hw hs
  unfold form_0000032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0000033 (u v w : ℝ) : ℝ :=
  (1142853097 / 1048576 : ℝ)*u^3 + (877710411 / 2097152 : ℝ)*u^2*v^1 + (2265158763 / 2097152 : ℝ)*u^2*w^1 + (2322940605 / 1048576 : ℝ)*u^1*v^2 + (5750344803 / 1048576 : ℝ)*u^1*v^1*w^1 + (3425194815 / 1048576 : ℝ)*u^1*w^2 + (185339503 / 131072 : ℝ)*v^3 + (4872715323 / 1048576 : ℝ)*v^2*w^1 + (10593940287 / 2097152 : ℝ)*v^1*w^2 + (3813892117 / 2097152 : ℝ)*w^3

private theorem form_0000033_pos : ConePositive form_0000033 := by
  intro u v w hu hv hw hs
  unfold form_0000033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000003 (u v w : ℝ) : ℝ :=
  (111736081 / 262144 : ℝ)*u^3 + (-167042163 / 65536 : ℝ)*u^2*v^1 + (684242535 / 262144 : ℝ)*u^2*w^1 + (2899502415 / 262144 : ℝ)*u^1*v^2 + (-464658717 / 131072 : ℝ)*u^1*v^1*w^1 + (515570901 / 131072 : ℝ)*u^1*w^2 + (155590551 / 65536 : ℝ)*v^3 + (2992582755 / 262144 : ℝ)*v^2*w^1 + (-129819309 / 131072 : ℝ)*v^1*w^2 + (28661611 / 16384 : ℝ)*w^3

private theorem form_000003_pos : ConePositive form_000003 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_000003 (u+v/2+w/2) (v/2) (w/2)) = form_0000030 := by
      funext u v w; dsimp [form_000003, form_0000030]; ring
    rw [he]
    exact form_0000030_pos
  · have he : (fun u v w : ℝ => form_000003 (u/2) (u/2+v+w/2) (w/2)) = form_0000031 := by
      funext u v w; dsimp [form_000003, form_0000031]; ring
    rw [he]
    exact form_0000031_pos
  · have he : (fun u v w : ℝ => form_000003 (u/2) (v/2) (u/2+v/2+w)) = form_0000032 := by
      funext u v w; dsimp [form_000003, form_0000032]; ring
    rw [he]
    exact form_0000032_pos
  · have he : (fun u v w : ℝ => form_000003 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0000033 := by
      funext u v w; dsimp [form_000003, form_0000033]; ring
    rw [he]
    exact form_0000033_pos

private def form_00000 (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (216351 / 32 : ℝ)*u^2*v^1 + (413595 / 32 : ℝ)*u^2*w^1 + (29889 / 4 : ℝ)*u^1*v^2 + (31491621 / 1024 : ℝ)*u^1*v^1*w^1 + (-12146169 / 256 : ℝ)*u^1*w^2 + (22403223 / 8192 : ℝ)*v^3 + (581246127 / 32768 : ℝ)*v^2*w^1 + (-347210619 / 8192 : ℝ)*v^1*w^2 + (1176569233 / 32768 : ℝ)*w^3

private theorem form_00000_pos : ConePositive form_00000 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00000 (u+v/2+w/2) (v/2) (w/2)) = form_000000 := by
      funext u v w; dsimp [form_00000, form_000000]; ring
    rw [he]
    exact form_000000_pos
  · have he : (fun u v w : ℝ => form_00000 (u/2) (u/2+v+w/2) (w/2)) = form_000001 := by
      funext u v w; dsimp [form_00000, form_000001]; ring
    rw [he]
    exact form_000001_pos
  · have he : (fun u v w : ℝ => form_00000 (u/2) (v/2) (u/2+v/2+w)) = form_000002 := by
      funext u v w; dsimp [form_00000, form_000002]; ring
    rw [he]
    exact form_000002_pos
  · have he : (fun u v w : ℝ => form_00000 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_000003 := by
      funext u v w; dsimp [form_00000, form_000003]; ring
    rw [he]
    exact form_000003_pos

private def form_000010 (u v w : ℝ) : ℝ :=
  (22403223 / 8192 : ℝ)*u^3 + (140416335 / 16384 : ℝ)*u^2*v^1 + (874072791 / 65536 : ℝ)*u^2*w^1 + (292996845 / 32768 : ℝ)*u^1*v^2 + (1850194485 / 65536 : ℝ)*u^1*v^1*w^1 + (1921137 / 1024 : ℝ)*u^1*w^2 + (203541741 / 65536 : ℝ)*v^3 + (3902054319 / 262144 : ℝ)*v^2*w^1 + (12995475 / 4096 : ℝ)*v^1*w^2 + (800867989 / 262144 : ℝ)*w^3

private theorem form_000010_pos : ConePositive form_000010 := by
  intro u v w hu hv hw hs
  unfold form_000010
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000011 (u v w : ℝ) : ℝ :=
  (203541741 / 65536 : ℝ)*u^3 + (158814189 / 16384 : ℝ)*u^2*v^1 + (4000580451 / 262144 : ℝ)*u^2*w^1 + (41261967 / 4096 : ℝ)*u^1*v^2 + (1050864633 / 32768 : ℝ)*u^1*v^1*w^1 + (618126915 / 131072 : ℝ)*u^1*w^2 + (3569751 / 1024 : ℝ)*v^3 + (275234715 / 16384 : ℝ)*v^2*w^1 + (196392441 / 32768 : ℝ)*v^1*w^2 + (142285661 / 32768 : ℝ)*w^3

private theorem form_000011_pos : ConePositive form_000011 := by
  intro u v w hu hv hw hs
  unfold form_000011
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000012 (u v w : ℝ) : ℝ :=
  (800867989 / 262144 : ℝ)*u^3 + (2742503295 / 262144 : ℝ)*u^2*v^1 + (2156698431 / 131072 : ℝ)*u^2*w^1 + (1539985083 / 131072 : ℝ)*u^1*v^2 + (299318607 / 8192 : ℝ)*u^1*v^1*w^1 + (1392432843 / 32768 : ℝ)*u^1*w^2 + (142285661 / 32768 : ℝ)*v^3 + (657321525 / 32768 : ℝ)*v^2*w^1 + (736163799 / 16384 : ℝ)*v^1*w^2 + (83713897 / 2048 : ℝ)*w^3

private theorem form_000012_pos : ConePositive form_000012 := by
  intro u v w hu hv hw hs
  unfold form_000012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000013 (u v w : ℝ) : ℝ :=
  (800867989 / 262144 : ℝ)*u^3 + (12995475 / 4096 : ℝ)*u^2*v^1 + (2742503295 / 262144 : ℝ)*u^2*w^1 + (3902054319 / 262144 : ℝ)*u^1*v^2 + (1033375749 / 131072 : ℝ)*u^1*v^1*w^1 + (1539985083 / 131072 : ℝ)*u^1*w^2 + (203541741 / 65536 : ℝ)*v^3 + (4000580451 / 262144 : ℝ)*v^2*w^1 + (618126915 / 131072 : ℝ)*v^1*w^2 + (142285661 / 32768 : ℝ)*w^3

private theorem form_000013_pos : ConePositive form_000013 := by
  intro u v w hu hv hw hs
  unfold form_000013
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00001 (u v w : ℝ) : ℝ :=
  (22403223 / 8192 : ℝ)*u^3 + (36603333 / 4096 : ℝ)*u^2*v^1 + (605234115 / 32768 : ℝ)*u^2*w^1 + (19843461 / 2048 : ℝ)*u^1*v^2 + (341647515 / 8192 : ℝ)*u^1*v^1*w^1 + (-616700685 / 16384 : ℝ)*u^1*w^2 + (3569751 / 1024 : ℝ)*v^3 + (189560691 / 8192 : ℝ)*v^2*w^1 + (-268402965 / 8192 : ℝ)*v^1*w^2 + (83713897 / 2048 : ℝ)*w^3

private theorem form_00001_pos : ConePositive form_00001 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00001 (u+v/2+w/2) (v/2) (w/2)) = form_000010 := by
      funext u v w; dsimp [form_00001, form_000010]; ring
    rw [he]
    exact form_000010_pos
  · have he : (fun u v w : ℝ => form_00001 (u/2) (u/2+v+w/2) (w/2)) = form_000011 := by
      funext u v w; dsimp [form_00001, form_000011]; ring
    rw [he]
    exact form_000011_pos
  · have he : (fun u v w : ℝ => form_00001 (u/2) (v/2) (u/2+v/2+w)) = form_000012 := by
      funext u v w; dsimp [form_00001, form_000012]; ring
    rw [he]
    exact form_000012_pos
  · have he : (fun u v w : ℝ => form_00001 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_000013 := by
      funext u v w; dsimp [form_00001, form_000013]; ring
    rw [he]
    exact form_000013_pos

private def form_00002 (u v w : ℝ) : ℝ :=
  (1176569233 / 32768 : ℝ)*u^3 + (3695574855 / 32768 : ℝ)*u^2*v^1 + (4307062515 / 16384 : ℝ)*u^2*w^1 + (1929238773 / 16384 : ℝ)*u^1*v^2 + (4432757343 / 8192 : ℝ)*u^1*v^1*w^1 + (5190297651 / 8192 : ℝ)*u^1*w^2 + (83713897 / 2048 : ℝ)*v^3 + (2277536493 / 8192 : ℝ)*v^2*w^1 + (5281439607 / 8192 : ℝ)*v^1*w^2 + (2051509969 / 4096 : ℝ)*w^3

private theorem form_00002_pos : ConePositive form_00002 := by
  intro u v w hu hv hw hs
  unfold form_00002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000030 (u v w : ℝ) : ℝ :=
  (1176569233 / 32768 : ℝ)*u^3 + (2140865223 / 65536 : ℝ)*u^2*v^1 + (3612641277 / 32768 : ℝ)*u^2*w^1 + (666634437 / 65536 : ℝ)*u^1*v^2 + (4524977793 / 65536 : ℝ)*u^1*v^1*w^1 + (14779334955 / 131072 : ℝ)*u^1*w^2 + (28661611 / 16384 : ℝ)*v^3 + (1505576637 / 131072 : ℝ)*v^2*w^1 + (9534166539 / 262144 : ℝ)*v^1*w^2 + (5035021993 / 131072 : ℝ)*w^3

private theorem form_000030_pos : ConePositive form_000030 := by
  intro u v w hu hv hw hs
  unfold form_000030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000031 (u v w : ℝ) : ℝ :=
  (28661611 / 16384 : ℝ)*u^3 + (21244227 / 65536 : ℝ)*u^2*v^1 + (860186427 / 131072 : ℝ)*u^2*w^1 + (850084803 / 65536 : ℝ)*u^1*v^2 + (143856633 / 65536 : ℝ)*u^1*v^1*w^1 + (2062704639 / 262144 : ℝ)*u^1*w^2 + (22403223 / 8192 : ℝ)*v^3 + (874072791 / 65536 : ℝ)*v^2*w^1 + (1921137 / 1024 : ℝ)*v^1*w^2 + (800867989 / 262144 : ℝ)*w^3

private theorem form_000031_pos : ConePositive form_000031 := by
  intro u v w hu hv hw hs
  unfold form_000031
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000032 (u v w : ℝ) : ℝ :=
  (5035021993 / 131072 : ℝ)*u^3 + (10185628587 / 262144 : ℝ)*u^2*v^1 + (15430797003 / 131072 : ℝ)*u^2*w^1 + (1986748767 / 131072 : ℝ)*u^1*v^2 + (5331880947 / 65536 : ℝ)*u^1*v^1*w^1 + (3938372301 / 32768 : ℝ)*u^1*w^2 + (800867989 / 262144 : ℝ)*v^3 + (2156698431 / 131072 : ℝ)*v^2*w^1 + (1392432843 / 32768 : ℝ)*v^1*w^2 + (83713897 / 2048 : ℝ)*w^3

private theorem form_000032_pos : ConePositive form_000032 := by
  intro u v w hu hv hw hs
  unfold form_000032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000033 (u v w : ℝ) : ℝ :=
  (5035021993 / 131072 : ℝ)*u^3 + (9534166539 / 262144 : ℝ)*u^2*v^1 + (10185628587 / 262144 : ℝ)*u^2*w^1 + (1505576637 / 131072 : ℝ)*u^1*v^2 + (3495364227 / 131072 : ℝ)*u^1*v^1*w^1 + (1986748767 / 131072 : ℝ)*u^1*w^2 + (28661611 / 16384 : ℝ)*v^3 + (860186427 / 131072 : ℝ)*v^2*w^1 + (2062704639 / 262144 : ℝ)*v^1*w^2 + (800867989 / 262144 : ℝ)*w^3

private theorem form_000033_pos : ConePositive form_000033 := by
  intro u v w hu hv hw hs
  unfold form_000033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00003 (u v w : ℝ) : ℝ :=
  (1176569233 / 32768 : ℝ)*u^3 + (-347210619 / 8192 : ℝ)*u^2*v^1 + (3695574855 / 32768 : ℝ)*u^2*w^1 + (581246127 / 32768 : ℝ)*u^1*v^2 + (-1311462285 / 16384 : ℝ)*u^1*v^1*w^1 + (1929238773 / 16384 : ℝ)*u^1*w^2 + (22403223 / 8192 : ℝ)*v^3 + (605234115 / 32768 : ℝ)*v^2*w^1 + (-616700685 / 16384 : ℝ)*v^1*w^2 + (83713897 / 2048 : ℝ)*w^3

private theorem form_00003_pos : ConePositive form_00003 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00003 (u+v/2+w/2) (v/2) (w/2)) = form_000030 := by
      funext u v w; dsimp [form_00003, form_000030]; ring
    rw [he]
    exact form_000030_pos
  · have he : (fun u v w : ℝ => form_00003 (u/2) (u/2+v+w/2) (w/2)) = form_000031 := by
      funext u v w; dsimp [form_00003, form_000031]; ring
    rw [he]
    exact form_000031_pos
  · have he : (fun u v w : ℝ => form_00003 (u/2) (v/2) (u/2+v/2+w)) = form_000032 := by
      funext u v w; dsimp [form_00003, form_000032]; ring
    rw [he]
    exact form_000032_pos
  · have he : (fun u v w : ℝ => form_00003 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_000033 := by
      funext u v w; dsimp [form_00003, form_000033]; ring
    rw [he]
    exact form_000033_pos

private def form_0000 (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (119151 / 16 : ℝ)*u^2*v^1 + (316395 / 16 : ℝ)*u^2*w^1 + (71361 / 8 : ℝ)*u^1*v^2 + (14443749 / 256 : ℝ)*u^1*v^1*w^1 + (-15066129 / 64 : ℝ)*u^1*w^2 + (3569751 / 1024 : ℝ)*v^3 + (146723679 / 4096 : ℝ)*v^2*w^1 + (-218272575 / 1024 : ℝ)*v^1*w^2 + (2051509969 / 4096 : ℝ)*w^3

private theorem form_0000_pos : ConePositive form_0000 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0000 (u+v/2+w/2) (v/2) (w/2)) = form_00000 := by
      funext u v w; dsimp [form_0000, form_00000]; ring
    rw [he]
    exact form_00000_pos
  · have he : (fun u v w : ℝ => form_0000 (u/2) (u/2+v+w/2) (w/2)) = form_00001 := by
      funext u v w; dsimp [form_0000, form_00001]; ring
    rw [he]
    exact form_00001_pos
  · have he : (fun u v w : ℝ => form_0000 (u/2) (v/2) (u/2+v/2+w)) = form_00002 := by
      funext u v w; dsimp [form_0000, form_00002]; ring
    rw [he]
    exact form_00002_pos
  · have he : (fun u v w : ℝ => form_0000 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00003 := by
      funext u v w; dsimp [form_0000, form_00003]; ring
    rw [he]
    exact form_00003_pos

private def form_000100 (u v w : ℝ) : ℝ :=
  (3569751 / 1024 : ℝ)*u^3 + (44412057 / 4096 : ℝ)*u^2*v^1 + (281534895 / 16384 : ℝ)*u^2*w^1 + (184014909 / 16384 : ℝ)*u^1*v^2 + (1176479811 / 32768 : ℝ)*u^1*v^1*w^1 + (123299835 / 16384 : ℝ)*u^1*w^2 + (253918395 / 65536 : ℝ)*v^3 + (4904550279 / 262144 : ℝ)*v^2*w^1 + (575592999 / 65536 : ℝ)*v^1*w^2 + (1470540241 / 262144 : ℝ)*w^3

private theorem form_000100_pos : ConePositive form_000100 := by
  intro u v w hu hv hw hs
  unfold form_000100
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000101 (u v w : ℝ) : ℝ :=
  (253918395 / 65536 : ℝ)*u^3 + (393725367 / 32768 : ℝ)*u^2*v^1 + (5007332475 / 262144 : ℝ)*u^2*w^1 + (203343777 / 16384 : ℝ)*u^1*v^2 + (2603439405 / 65536 : ℝ)*u^1*v^1*w^1 + (1350274683 / 131072 : ℝ)*u^1*w^2 + (34978797 / 8192 : ℝ)*v^3 + (1350886635 / 65536 : ℝ)*v^2*w^1 + (756128877 / 65536 : ℝ)*v^1*w^2 + (224666927 / 32768 : ℝ)*w^3

private theorem form_000101_pos : ConePositive form_000101 := by
  intro u v w hu hv hw hs
  unfold form_000101
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000102 (u v w : ℝ) : ℝ :=
  (1470540241 / 262144 : ℝ)*u^3 + (4741195359 / 262144 : ℝ)*u^2*v^1 + (3425222043 / 131072 : ℝ)*u^2*w^1 + (2534020053 / 131072 : ℝ)*u^1*v^2 + (3654116217 / 65536 : ℝ)*u^1*v^1*w^1 + (3564962943 / 65536 : ℝ)*u^1*w^2 + (224666927 / 32768 : ℝ)*v^3 + (1939874247 / 65536 : ℝ)*v^2*w^1 + (3718377375 / 65536 : ℝ)*v^1*w^2 + (1496049109 / 32768 : ℝ)*w^3

private theorem form_000102_pos : ConePositive form_000102 := by
  intro u v w hu hv hw hs
  unfold form_000102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000103 (u v w : ℝ) : ℝ :=
  (1470540241 / 262144 : ℝ)*u^3 + (575592999 / 65536 : ℝ)*u^2*v^1 + (4741195359 / 262144 : ℝ)*u^2*w^1 + (4904550279 / 262144 : ℝ)*u^1*v^2 + (2501003031 / 131072 : ℝ)*u^1*v^1*w^1 + (2534020053 / 131072 : ℝ)*u^1*w^2 + (253918395 / 65536 : ℝ)*v^3 + (5007332475 / 262144 : ℝ)*v^2*w^1 + (1350274683 / 131072 : ℝ)*v^1*w^2 + (224666927 / 32768 : ℝ)*w^3

private theorem form_000103_pos : ConePositive form_000103 := by
  intro u v w hu hv hw hs
  unfold form_000103
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00010 (u v w : ℝ) : ℝ :=
  (3569751 / 1024 : ℝ)*u^3 + (22993551 / 2048 : ℝ)*u^2*v^1 + (195860871 / 8192 : ℝ)*u^2*w^1 + (49203693 / 4096 : ℝ)*u^1*v^2 + (429461613 / 8192 : ℝ)*u^1*v^1*w^1 + (-3606189 / 128 : ℝ)*u^1*w^2 + (34978797 / 8192 : ℝ)*v^3 + (931141071 / 32768 : ℝ)*v^2*w^1 + (-24055311 / 1024 : ℝ)*v^1*w^2 + (1496049109 / 32768 : ℝ)*w^3

private theorem form_00010_pos : ConePositive form_00010 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00010 (u+v/2+w/2) (v/2) (w/2)) = form_000100 := by
      funext u v w; dsimp [form_00010, form_000100]; ring
    rw [he]
    exact form_000100_pos
  · have he : (fun u v w : ℝ => form_00010 (u/2) (u/2+v+w/2) (w/2)) = form_000101 := by
      funext u v w; dsimp [form_00010, form_000101]; ring
    rw [he]
    exact form_000101_pos
  · have he : (fun u v w : ℝ => form_00010 (u/2) (v/2) (u/2+v/2+w)) = form_000102 := by
      funext u v w; dsimp [form_00010, form_000102]; ring
    rw [he]
    exact form_000102_pos
  · have he : (fun u v w : ℝ => form_00010 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_000103 := by
      funext u v w; dsimp [form_00010, form_000103]; ring
    rw [he]
    exact form_000103_pos

private def form_000110 (u v w : ℝ) : ℝ :=
  (34978797 / 8192 : ℝ)*u^3 + (216401787 / 16384 : ℝ)*u^2*v^1 + (1377002655 / 65536 : ℝ)*u^2*w^1 + (445957407 / 32768 : ℝ)*u^1*v^2 + (2852722467 / 65536 : ℝ)*u^1*v^1*w^1 + (213663597 / 16384 : ℝ)*u^1*w^2 + (306125649 / 65536 : ℝ)*v^3 + (5899851927 / 262144 : ℝ)*v^2*w^1 + (467084721 / 32768 : ℝ)*v^1*w^2 + (2118373381 / 262144 : ℝ)*w^3

private theorem form_000110_pos : ConePositive form_000110 := by
  intro u v w hu hv hw hs
  unfold form_000110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000111 (u v w : ℝ) : ℝ :=
  (306125649 / 65536 : ℝ)*u^3 + (118104885 / 8192 : ℝ)*u^2*v^1 + (6005700459 / 262144 : ℝ)*u^2*w^1 + (15178995 / 1024 : ℝ)*u^1*v^2 + (775090665 / 16384 : ℝ)*u^1*v^1*w^1 + (2063054811 / 131072 : ℝ)*u^1*w^2 + (649863 / 128 : ℝ)*v^3 + (99883971 / 4096 : ℝ)*v^2*w^1 + (277372905 / 16384 : ℝ)*v^1*w^2 + (76042397 / 8192 : ℝ)*w^3

private theorem form_000111_pos : ConePositive form_000111 := by
  intro u v w hu hv hw hs
  unfold form_000111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000112 (u v w : ℝ) : ℝ :=
  (2118373381 / 262144 : ℝ)*u^3 + (6673180359 / 262144 : ℝ)*u^2*v^1 + (4645811367 / 131072 : ℝ)*u^2*w^1 + (3494106627 / 131072 : ℝ)*u^1*v^2 + (2432577213 / 32768 : ℝ)*u^1*v^1*w^1 + (2156752623 / 32768 : ℝ)*u^1*w^2 + (76042397 / 8192 : ℝ)*v^3 + (635135859 / 16384 : ℝ)*v^2*w^1 + (34845681 / 512 : ℝ)*v^1*w^2 + (205769009 / 4096 : ℝ)*w^3

private theorem form_000112_pos : ConePositive form_000112 := by
  intro u v w hu hv hw hs
  unfold form_000112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000113 (u v w : ℝ) : ℝ :=
  (2118373381 / 262144 : ℝ)*u^3 + (467084721 / 32768 : ℝ)*u^2*v^1 + (6673180359 / 262144 : ℝ)*u^2*w^1 + (5899851927 / 262144 : ℝ)*u^1*v^2 + (3931084761 / 131072 : ℝ)*u^1*v^1*w^1 + (3494106627 / 131072 : ℝ)*u^1*w^2 + (306125649 / 65536 : ℝ)*v^3 + (6005700459 / 262144 : ℝ)*v^2*w^1 + (2063054811 / 131072 : ℝ)*v^1*w^2 + (76042397 / 8192 : ℝ)*w^3

private theorem form_000113_pos : ConePositive form_000113 := by
  intro u v w hu hv hw hs
  unfold form_000113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00011 (u v w : ℝ) : ℝ :=
  (34978797 / 8192 : ℝ)*u^3 + (27866349 / 2048 : ℝ)*u^2*v^1 + (957257091 / 32768 : ℝ)*u^2*w^1 + (7380639 / 512 : ℝ)*u^1*v^2 + (257464557 / 4096 : ℝ)*u^1*v^1*w^1 + (-312475485 / 16384 : ℝ)*u^1*w^2 + (649863 / 128 : ℝ)*v^3 + (68690547 / 2048 : ℝ)*v^2*w^1 + (-59776131 / 4096 : ℝ)*v^1*w^2 + (205769009 / 4096 : ℝ)*w^3

private theorem form_00011_pos : ConePositive form_00011 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00011 (u+v/2+w/2) (v/2) (w/2)) = form_000110 := by
      funext u v w; dsimp [form_00011, form_000110]; ring
    rw [he]
    exact form_000110_pos
  · have he : (fun u v w : ℝ => form_00011 (u/2) (u/2+v+w/2) (w/2)) = form_000111 := by
      funext u v w; dsimp [form_00011, form_000111]; ring
    rw [he]
    exact form_000111_pos
  · have he : (fun u v w : ℝ => form_00011 (u/2) (v/2) (u/2+v/2+w)) = form_000112 := by
      funext u v w; dsimp [form_00011, form_000112]; ring
    rw [he]
    exact form_000112_pos
  · have he : (fun u v w : ℝ => form_00011 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_000113 := by
      funext u v w; dsimp [form_00011, form_000113]; ring
    rw [he]
    exact form_000113_pos

private def form_00012 (u v w : ℝ) : ℝ :=
  (1496049109 / 32768 : ℝ)*u^3 + (4641561759 / 32768 : ℝ)*u^2*v^1 + (4949739519 / 16384 : ℝ)*u^2*w^1 + (2395857147 / 16384 : ℝ)*u^1*v^2 + (79147095 / 128 : ℝ)*u^1*v^1*w^1 + (2803596291 / 4096 : ℝ)*u^1*w^2 + (205769009 / 4096 : ℝ)*v^3 + (1294390185 / 4096 : ℝ)*v^2*w^1 + (1422856863 / 2048 : ℝ)*v^1*w^2 + (16712681 / 32 : ℝ)*w^3

private theorem form_00012_pos : ConePositive form_00012 := by
  intro u v w hu hv hw hs
  unfold form_00012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000130 (u v w : ℝ) : ℝ :=
  (1496049109 / 32768 : ℝ)*u^3 + (3718377375 / 65536 : ℝ)*u^2*v^1 + (4564854543 / 32768 : ℝ)*u^2*w^1 + (1939874247 / 65536 : ℝ)*u^1*v^2 + (7662387027 / 65536 : ℝ)*u^1*v^1*w^1 + (18562985139 / 131072 : ℝ)*u^1*w^2 + (224666927 / 32768 : ℝ)*v^3 + (4041731565 / 131072 : ℝ)*v^2*w^1 + (15773160003 / 262144 : ℝ)*v^1*w^2 + (6287738617 / 131072 : ℝ)*w^3

private theorem form_000130_pos : ConePositive form_000130 := by
  intro u v w hu hv hw hs
  unfold form_000130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000131 (u v w : ℝ) : ℝ :=
  (224666927 / 32768 : ℝ)*u^3 + (756128877 / 65536 : ℝ)*u^2*v^1 + (2857986195 / 131072 : ℝ)*u^2*w^1 + (1350886635 / 65536 : ℝ)*u^1*v^2 + (1610591619 / 65536 : ℝ)*u^1*v^1*w^1 + (6037059927 / 262144 : ℝ)*u^1*w^2 + (34978797 / 8192 : ℝ)*v^3 + (1377002655 / 65536 : ℝ)*v^2*w^1 + (213663597 / 16384 : ℝ)*v^1*w^2 + (2118373381 / 262144 : ℝ)*w^3

private theorem form_000131_pos : ConePositive form_000131 := by
  intro u v w hu hv hw hs
  unfold form_000131
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000132 (u v w : ℝ) : ℝ :=
  (6287738617 / 131072 : ℝ)*u^3 + (16373621427 / 262144 : ℝ)*u^2*v^1 + (19163446563 / 131072 : ℝ)*u^2*w^1 + (4486781259 / 131072 : ℝ)*u^1*v^2 + (8407667433 / 65536 : ℝ)*u^1*v^1*w^1 + (4865085255 / 32768 : ℝ)*u^1*w^2 + (2118373381 / 262144 : ℝ)*v^3 + (4645811367 / 131072 : ℝ)*v^2*w^1 + (2156752623 / 32768 : ℝ)*v^1*w^2 + (205769009 / 4096 : ℝ)*w^3

private theorem form_000132_pos : ConePositive form_000132 := by
  intro u v w hu hv hw hs
  unfold form_000132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000133 (u v w : ℝ) : ℝ :=
  (6287738617 / 131072 : ℝ)*u^3 + (15773160003 / 262144 : ℝ)*u^2*v^1 + (16373621427 / 262144 : ℝ)*u^2*w^1 + (4041731565 / 131072 : ℝ)*u^1*v^2 + (8531849079 / 131072 : ℝ)*u^1*v^1*w^1 + (4486781259 / 131072 : ℝ)*u^1*w^2 + (224666927 / 32768 : ℝ)*v^3 + (2857986195 / 131072 : ℝ)*v^2*w^1 + (6037059927 / 262144 : ℝ)*v^1*w^2 + (2118373381 / 262144 : ℝ)*w^3

private theorem form_000133_pos : ConePositive form_000133 := by
  intro u v w hu hv hw hs
  unfold form_000133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00013 (u v w : ℝ) : ℝ :=
  (1496049109 / 32768 : ℝ)*u^3 + (-24055311 / 1024 : ℝ)*u^2*v^1 + (4641561759 / 32768 : ℝ)*u^2*w^1 + (931141071 / 32768 : ℝ)*u^1*v^2 + (-697552107 / 16384 : ℝ)*u^1*v^1*w^1 + (2395857147 / 16384 : ℝ)*u^1*w^2 + (34978797 / 8192 : ℝ)*v^3 + (957257091 / 32768 : ℝ)*v^2*w^1 + (-312475485 / 16384 : ℝ)*v^1*w^2 + (205769009 / 4096 : ℝ)*w^3

private theorem form_00013_pos : ConePositive form_00013 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00013 (u+v/2+w/2) (v/2) (w/2)) = form_000130 := by
      funext u v w; dsimp [form_00013, form_000130]; ring
    rw [he]
    exact form_000130_pos
  · have he : (fun u v w : ℝ => form_00013 (u/2) (u/2+v+w/2) (w/2)) = form_000131 := by
      funext u v w; dsimp [form_00013, form_000131]; ring
    rw [he]
    exact form_000131_pos
  · have he : (fun u v w : ℝ => form_00013 (u/2) (v/2) (u/2+v/2+w)) = form_000132 := by
      funext u v w; dsimp [form_00013, form_000132]; ring
    rw [he]
    exact form_000132_pos
  · have he : (fun u v w : ℝ => form_00013 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_000133 := by
      funext u v w; dsimp [form_00013, form_000133]; ring
    rw [he]
    exact form_000133_pos

private def form_0001 (u v w : ℝ) : ℝ :=
  (3569751 / 1024 : ℝ)*u^3 + (6142149 / 512 : ℝ)*u^2*v^1 + (153023859 / 4096 : ℝ)*u^2*w^1 + (3481461 / 256 : ℝ)*u^1*v^2 + (92231775 / 1024 : ℝ)*u^1*v^1*w^1 + (-405238461 / 2048 : ℝ)*u^1*w^2 + (649863 / 128 : ℝ)*v^3 + (53093835 / 1024 : ℝ)*v^2*w^1 + (-181560513 / 1024 : ℝ)*v^1*w^2 + (16712681 / 32 : ℝ)*w^3

private theorem form_0001_pos : ConePositive form_0001 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0001 (u+v/2+w/2) (v/2) (w/2)) = form_00010 := by
      funext u v w; dsimp [form_0001, form_00010]; ring
    rw [he]
    exact form_00010_pos
  · have he : (fun u v w : ℝ => form_0001 (u/2) (u/2+v+w/2) (w/2)) = form_00011 := by
      funext u v w; dsimp [form_0001, form_00011]; ring
    rw [he]
    exact form_00011_pos
  · have he : (fun u v w : ℝ => form_0001 (u/2) (v/2) (u/2+v/2+w)) = form_00012 := by
      funext u v w; dsimp [form_0001, form_00012]; ring
    rw [he]
    exact form_00012_pos
  · have he : (fun u v w : ℝ => form_0001 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00013 := by
      funext u v w; dsimp [form_0001, form_00013]; ring
    rw [he]
    exact form_00013_pos

private def form_0002 (u v w : ℝ) : ℝ :=
  (2051509969 / 4096 : ℝ)*u^3 + (6245671863 / 4096 : ℝ)*u^2*v^1 + (6636646035 / 2048 : ℝ)*u^2*w^1 + (3166717317 / 2048 : ℝ)*u^1*v^2 + (6710511555 / 1024 : ℝ)*u^1*v^1*w^1 + (7139011443 / 1024 : ℝ)*u^1*w^2 + (16712681 / 32 : ℝ)*v^3 + (3390395265 / 1024 : ℝ)*v^2*w^1 + (7197005391 / 1024 : ℝ)*v^1*w^2 + (2552838577 / 512 : ℝ)*w^3

private theorem form_0002_pos : ConePositive form_0002 := by
  intro u v w hu hv hw hs
  unfold form_0002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00030 (u v w : ℝ) : ℝ :=
  (2051509969 / 4096 : ℝ)*u^3 + (5281439607 / 8192 : ℝ)*u^2*v^1 + (6200100885 / 4096 : ℝ)*u^2*w^1 + (2277536493 / 8192 : ℝ)*u^1*v^2 + (10685194857 / 8192 : ℝ)*u^1*v^1*w^1 + (24979308267 / 16384 : ℝ)*u^1*w^2 + (83713897 / 2048 : ℝ)*v^3 + (4634967741 / 16384 : ℝ)*v^2*w^1 + (21611907819 / 32768 : ℝ)*v^1*w^2 + (8384919817 / 16384 : ℝ)*w^3

private theorem form_00030_pos : ConePositive form_00030 := by
  intro u v w hu hv hw hs
  unfold form_00030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000310 (u v w : ℝ) : ℝ :=
  (83713897 / 2048 : ℝ)*u^3 + (736163799 / 16384 : ℝ)*u^2*v^1 + (4098161811 / 32768 : ℝ)*u^2*w^1 + (657321525 / 32768 : ℝ)*u^1*v^2 + (1531011909 / 16384 : ℝ)*u^1*v^1*w^1 + (16709113083 / 131072 : ℝ)*u^1*w^2 + (142285661 / 32768 : ℝ)*v^3 + (2796728949 / 131072 : ℝ)*v^2*w^1 + (12714988587 / 262144 : ℝ)*v^1*w^2 + (5674130461 / 131072 : ℝ)*w^3

private theorem form_000310_pos : ConePositive form_000310 := by
  intro u v w hu hv hw hs
  unfold form_000310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000311 (u v w : ℝ) : ℝ :=
  (142285661 / 32768 : ℝ)*u^3 + (196392441 / 32768 : ℝ)*u^2*v^1 + (1874870781 / 131072 : ℝ)*u^2*w^1 + (275234715 / 16384 : ℝ)*u^1*v^2 + (442859109 / 32768 : ℝ)*u^1*v^1*w^1 + (4082046087 / 262144 : ℝ)*u^1*w^2 + (3569751 / 1024 : ℝ)*v^3 + (281534895 / 16384 : ℝ)*v^2*w^1 + (123299835 / 16384 : ℝ)*v^1*w^2 + (1470540241 / 262144 : ℝ)*w^3

private theorem form_000311_pos : ConePositive form_000311 := by
  intro u v w hu hv hw hs
  unfold form_000311
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000312 (u v w : ℝ) : ℝ :=
  (5674130461 / 131072 : ℝ)*u^3 + (13341545187 / 262144 : ℝ)*u^2*v^1 + (17335669683 / 131072 : ℝ)*u^2*w^1 + (3260434725 / 131072 : ℝ)*u^1*v^2 + (215657241 / 2048 : ℝ)*u^1*v^1*w^1 + (4411440111 / 32768 : ℝ)*u^1*w^2 + (1470540241 / 262144 : ℝ)*v^3 + (3425222043 / 131072 : ℝ)*v^2*w^1 + (3564962943 / 65536 : ℝ)*v^1*w^2 + (1496049109 / 32768 : ℝ)*w^3

private theorem form_000312_pos : ConePositive form_000312 := by
  intro u v w hu hv hw hs
  unfold form_000312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_000313 (u v w : ℝ) : ℝ :=
  (5674130461 / 131072 : ℝ)*u^3 + (12714988587 / 262144 : ℝ)*u^2*v^1 + (13341545187 / 262144 : ℝ)*u^2*w^1 + (2796728949 / 131072 : ℝ)*u^1*v^2 + (6060351213 / 131072 : ℝ)*u^1*v^1*w^1 + (3260434725 / 131072 : ℝ)*u^1*w^2 + (142285661 / 32768 : ℝ)*v^3 + (1874870781 / 131072 : ℝ)*v^2*w^1 + (4082046087 / 262144 : ℝ)*v^1*w^2 + (1470540241 / 262144 : ℝ)*w^3

private theorem form_000313_pos : ConePositive form_000313 := by
  intro u v w hu hv hw hs
  unfold form_000313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00031 (u v w : ℝ) : ℝ :=
  (83713897 / 2048 : ℝ)*u^3 + (-268402965 / 8192 : ℝ)*u^2*v^1 + (2089028283 / 16384 : ℝ)*u^2*w^1 + (189560691 / 8192 : ℝ)*u^1*v^2 + (-499332063 / 8192 : ℝ)*u^1*v^1*w^1 + (4334732895 / 32768 : ℝ)*u^1*w^2 + (3569751 / 1024 : ℝ)*v^3 + (195860871 / 8192 : ℝ)*v^2*w^1 + (-3606189 / 128 : ℝ)*v^1*w^2 + (1496049109 / 32768 : ℝ)*w^3

private theorem form_00031_pos : ConePositive form_00031 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00031 (u+v/2+w/2) (v/2) (w/2)) = form_000310 := by
      funext u v w; dsimp [form_00031, form_000310]; ring
    rw [he]
    exact form_000310_pos
  · have he : (fun u v w : ℝ => form_00031 (u/2) (u/2+v+w/2) (w/2)) = form_000311 := by
      funext u v w; dsimp [form_00031, form_000311]; ring
    rw [he]
    exact form_000311_pos
  · have he : (fun u v w : ℝ => form_00031 (u/2) (v/2) (u/2+v/2+w)) = form_000312 := by
      funext u v w; dsimp [form_00031, form_000312]; ring
    rw [he]
    exact form_000312_pos
  · have he : (fun u v w : ℝ => form_00031 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_000313 := by
      funext u v w; dsimp [form_00031, form_000313]; ring
    rw [he]
    exact form_000313_pos

private def form_00032 (u v w : ℝ) : ℝ :=
  (8384919817 / 16384 : ℝ)*u^3 + (21962810187 / 32768 : ℝ)*u^2*v^1 + (25330210635 / 16384 : ℝ)*u^2*w^1 + (4873032303 / 16384 : ℝ)*u^1*v^2 + (11098710603 / 8192 : ℝ)*u^1*v^1*w^1 + (6375552069 / 4096 : ℝ)*u^1*w^2 + (1496049109 / 32768 : ℝ)*v^3 + (4949739519 / 16384 : ℝ)*v^2*w^1 + (2803596291 / 4096 : ℝ)*v^1*w^2 + (16712681 / 32 : ℝ)*w^3

private theorem form_00032_pos : ConePositive form_00032 := by
  intro u v w hu hv hw hs
  unfold form_00032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00033 (u v w : ℝ) : ℝ :=
  (8384919817 / 16384 : ℝ)*u^3 + (21611907819 / 32768 : ℝ)*u^2*v^1 + (21962810187 / 32768 : ℝ)*u^2*w^1 + (4634967741 / 16384 : ℝ)*u^1*v^2 + (9511453587 / 16384 : ℝ)*u^1*v^1*w^1 + (4873032303 / 16384 : ℝ)*u^1*w^2 + (83713897 / 2048 : ℝ)*v^3 + (2089028283 / 16384 : ℝ)*v^2*w^1 + (4334732895 / 32768 : ℝ)*v^1*w^2 + (1496049109 / 32768 : ℝ)*w^3

private theorem form_00033_pos : ConePositive form_00033 := by
  intro u v w hu hv hw hs
  unfold form_00033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0003 (u v w : ℝ) : ℝ :=
  (2051509969 / 4096 : ℝ)*u^3 + (-218272575 / 1024 : ℝ)*u^2*v^1 + (6245671863 / 4096 : ℝ)*u^2*w^1 + (146723679 / 4096 : ℝ)*u^1*v^2 + (-841916613 / 2048 : ℝ)*u^1*v^1*w^1 + (3166717317 / 2048 : ℝ)*u^1*w^2 + (3569751 / 1024 : ℝ)*v^3 + (153023859 / 4096 : ℝ)*v^2*w^1 + (-405238461 / 2048 : ℝ)*v^1*w^2 + (16712681 / 32 : ℝ)*w^3

private theorem form_0003_pos : ConePositive form_0003 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0003 (u+v/2+w/2) (v/2) (w/2)) = form_00030 := by
      funext u v w; dsimp [form_0003, form_00030]; ring
    rw [he]
    exact form_00030_pos
  · have he : (fun u v w : ℝ => form_0003 (u/2) (u/2+v+w/2) (w/2)) = form_00031 := by
      funext u v w; dsimp [form_0003, form_00031]; ring
    rw [he]
    exact form_00031_pos
  · have he : (fun u v w : ℝ => form_0003 (u/2) (v/2) (u/2+v/2+w)) = form_00032 := by
      funext u v w; dsimp [form_0003, form_00032]; ring
    rw [he]
    exact form_00032_pos
  · have he : (fun u v w : ℝ => form_0003 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00033 := by
      funext u v w; dsimp [form_0003, form_00033]; ring
    rw [he]
    exact form_00033_pos

private def form_000 (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (70551 / 8 : ℝ)*u^2*v^1 + (267795 / 8 : ℝ)*u^2*w^1 + (47871 / 4 : ℝ)*u^1*v^2 + (8252613 / 64 : ℝ)*u^1*v^1*w^1 + (-16234509 / 16 : ℝ)*u^1*w^2 + (649863 / 128 : ℝ)*v^3 + (45295479 / 512 : ℝ)*v^2*w^1 + (-115377585 / 128 : ℝ)*v^1*w^2 + (2552838577 / 512 : ℝ)*w^3

private theorem form_000_pos : ConePositive form_000 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_000 (u+v/2+w/2) (v/2) (w/2)) = form_0000 := by
      funext u v w; dsimp [form_000, form_0000]; ring
    rw [he]
    exact form_0000_pos
  · have he : (fun u v w : ℝ => form_000 (u/2) (u/2+v+w/2) (w/2)) = form_0001 := by
      funext u v w; dsimp [form_000, form_0001]; ring
    rw [he]
    exact form_0001_pos
  · have he : (fun u v w : ℝ => form_000 (u/2) (v/2) (u/2+v/2+w)) = form_0002 := by
      funext u v w; dsimp [form_000, form_0002]; ring
    rw [he]
    exact form_0002_pos
  · have he : (fun u v w : ℝ => form_000 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0003 := by
      funext u v w; dsimp [form_000, form_0003]; ring
    rw [he]
    exact form_0003_pos

private def form_001000 (u v w : ℝ) : ℝ :=
  (649863 / 128 : ℝ)*u^3 + (16014429 / 1024 : ℝ)*u^2*v^1 + (101554839 / 4096 : ℝ)*u^2*w^1 + (131471829 / 8192 : ℝ)*u^1*v^2 + (836478459 / 16384 : ℝ)*u^1*v^1*w^1 + (150691665 / 8192 : ℝ)*u^1*w^2 + (359568639 / 65536 : ℝ)*v^3 + (6880820895 / 262144 : ℝ)*v^2*w^1 + (1281872337 / 65536 : ℝ)*v^1*w^2 + (2741987953 / 262144 : ℝ)*w^3

private theorem form_001000_pos : ConePositive form_001000 := by
  intro u v w hu hv hw hs
  unfold form_001000
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001001 (u v w : ℝ) : ℝ :=
  (359568639 / 65536 : ℝ)*u^3 + (552818601 / 32768 : ℝ)*u^2*v^1 + (6988546035 / 262144 : ℝ)*u^2*w^1 + (283162149 / 16384 : ℝ)*u^1*v^2 + (3588929847 / 65536 : ℝ)*u^1*v^1*w^1 + (2752898115 / 131072 : ℝ)*u^1*w^2 + (48320955 / 8192 : ℝ)*v^3 + (1840924971 / 65536 : ℝ)*v^2*w^1 + (1451088519 / 65536 : ℝ)*v^1*w^2 + (95124053 / 8192 : ℝ)*w^3

private theorem form_001001_pos : ConePositive form_001001 := by
  intro u v w hu hv hw hs
  unfold form_001001
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001002 (u v w : ℝ) : ℝ :=
  (2741987953 / 262144 : ℝ)*u^3 + (8531319927 / 262144 : ℝ)*u^2*v^1 + (5814897219 / 131072 : ℝ)*u^2*w^1 + (4416675621 / 131072 : ℝ)*u^1*v^2 + (6024094299 / 65536 : ℝ)*u^1*v^1*w^1 + (5028708003 / 65536 : ℝ)*u^1*w^2 + (95124053 / 8192 : ℝ)*v^3 + (3114866025 / 65536 : ℝ)*v^2*w^1 + (5168479983 / 65536 : ℝ)*v^1*w^2 + (1789433809 / 32768 : ℝ)*w^3

private theorem form_001002_pos : ConePositive form_001002 := by
  intro u v w hu hv hw hs
  unfold form_001002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001003 (u v w : ℝ) : ℝ :=
  (2741987953 / 262144 : ℝ)*u^3 + (1281872337 / 65536 : ℝ)*u^2*v^1 + (8531319927 / 262144 : ℝ)*u^2*w^1 + (6880820895 / 262144 : ℝ)*u^1*v^2 + (5316482571 / 131072 : ℝ)*u^1*v^1*w^1 + (4416675621 / 131072 : ℝ)*u^1*w^2 + (359568639 / 65536 : ℝ)*v^3 + (6988546035 / 262144 : ℝ)*v^2*w^1 + (2752898115 / 131072 : ℝ)*v^1*w^2 + (95124053 / 8192 : ℝ)*w^3

private theorem form_001003_pos : ConePositive form_001003 := by
  intro u v w hu hv hw hs
  unfold form_001003
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00100 (u v w : ℝ) : ℝ :=
  (649863 / 128 : ℝ)*u^3 + (8216073 / 512 : ℝ)*u^2*v^1 + (70361415 / 2048 : ℝ)*u^2*w^1 + (34549821 / 2048 : ℝ)*u^1*v^2 + (298801935 / 4096 : ℝ)*u^1*v^1*w^1 + (-21224589 / 2048 : ℝ)*u^1*w^2 + (48320955 / 8192 : ℝ)*v^3 + (1261073511 / 32768 : ℝ)*v^2*w^1 + (-49955361 / 8192 : ℝ)*v^1*w^2 + (1789433809 / 32768 : ℝ)*w^3

private theorem form_00100_pos : ConePositive form_00100 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00100 (u+v/2+w/2) (v/2) (w/2)) = form_001000 := by
      funext u v w; dsimp [form_00100, form_001000]; ring
    rw [he]
    exact form_001000_pos
  · have he : (fun u v w : ℝ => form_00100 (u/2) (u/2+v+w/2) (w/2)) = form_001001 := by
      funext u v w; dsimp [form_00100, form_001001]; ring
    rw [he]
    exact form_001001_pos
  · have he : (fun u v w : ℝ => form_00100 (u/2) (v/2) (u/2+v/2+w)) = form_001002 := by
      funext u v w; dsimp [form_00100, form_001002]; ring
    rw [he]
    exact form_001002_pos
  · have he : (fun u v w : ℝ => form_00100 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_001003 := by
      funext u v w; dsimp [form_00100, form_001003]; ring
    rw [he]
    exact form_001003_pos

private def form_001010 (u v w : ℝ) : ℝ :=
  (48320955 / 8192 : ℝ)*u^3 + (296689311 / 16384 : ℝ)*u^2*v^1 + (1867979295 / 65536 : ℝ)*u^2*w^1 + (606927249 / 32768 : ℝ)*u^1*v^2 + (3828964545 / 65536 : ℝ)*u^1*v^1*w^1 + (193006443 / 8192 : ℝ)*u^1*w^2 + (413652501 / 65536 : ℝ)*v^3 + (7840318815 / 262144 : ℝ)*v^2*w^1 + (404229273 / 16384 : ℝ)*v^1*w^2 + (3339004501 / 262144 : ℝ)*w^3

private theorem form_001010_pos : ConePositive form_001010 := by
  intro u v w hu hv hw hs
  unfold form_001010
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001011 (u v w : ℝ) : ℝ :=
  (413652501 / 65536 : ℝ)*u^3 + (317015127 / 16384 : ℝ)*u^2*v^1 + (7948730835 / 262144 : ℝ)*u^2*w^1 + (80948079 / 4096 : ℝ)*u^1*v^2 + (2032785891 / 32768 : ℝ)*u^1*v^1*w^1 + (3416235411 / 131072 : ℝ)*u^1*w^2 + (6886701 / 1024 : ℝ)*v^3 + (519361587 / 16384 : ℝ)*v^2*w^1 + (889567491 / 32768 : ℝ)*v^1*w^2 + (453349367 / 32768 : ℝ)*w^3

private theorem form_001011_pos : ConePositive form_001011 := by
  intro u v w hu hv hw hs
  unfold form_001011
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001012 (u v w : ℝ) : ℝ :=
  (3339004501 / 262144 : ℝ)*u^3 + (10308475695 / 262144 : ℝ)*u^2*v^1 + (6928910415 / 131072 : ℝ)*u^2*w^1 + (5298157851 / 131072 : ℝ)*u^1*v^2 + (1781841663 / 16384 : ℝ)*u^1*v^1*w^1 + (2854393311 / 32768 : ℝ)*u^1*w^2 + (453349367 / 32768 : ℝ)*v^3 + (1830528711 / 32768 : ℝ)*v^2*w^1 + (1460322807 / 16384 : ℝ)*v^1*w^2 + (240699611 / 4096 : ℝ)*w^3

private theorem form_001012_pos : ConePositive form_001012 := by
  intro u v w hu hv hw hs
  unfold form_001012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001013 (u v w : ℝ) : ℝ :=
  (3339004501 / 262144 : ℝ)*u^3 + (404229273 / 16384 : ℝ)*u^2*v^1 + (10308475695 / 262144 : ℝ)*u^2*w^1 + (7840318815 / 262144 : ℝ)*u^1*v^2 + (6650058093 / 131072 : ℝ)*u^1*v^1*w^1 + (5298157851 / 131072 : ℝ)*u^1*w^2 + (413652501 / 65536 : ℝ)*v^3 + (7948730835 / 262144 : ℝ)*v^2*w^1 + (3416235411 / 131072 : ℝ)*v^1*w^2 + (453349367 / 32768 : ℝ)*w^3

private theorem form_001013_pos : ConePositive form_001013 := by
  intro u v w hu hv hw hs
  unfold form_001013
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00101 (u v w : ℝ) : ℝ :=
  (48320955 / 8192 : ℝ)*u^3 + (75863223 / 4096 : ℝ)*u^2*v^1 + (1288127835 / 32768 : ℝ)*u^2*w^1 + (39627873 / 2048 : ℝ)*u^1*v^2 + (677039733 / 8192 : ℝ)*u^1*v^1*w^1 + (-34002021 / 16384 : ℝ)*u^1*w^2 + (6886701 / 1024 : ℝ)*v^3 + (354080763 / 8192 : ℝ)*v^2*w^1 + (16125141 / 8192 : ℝ)*v^1*w^2 + (240699611 / 4096 : ℝ)*w^3

private theorem form_00101_pos : ConePositive form_00101 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00101 (u+v/2+w/2) (v/2) (w/2)) = form_001010 := by
      funext u v w; dsimp [form_00101, form_001010]; ring
    rw [he]
    exact form_001010_pos
  · have he : (fun u v w : ℝ => form_00101 (u/2) (u/2+v+w/2) (w/2)) = form_001011 := by
      funext u v w; dsimp [form_00101, form_001011]; ring
    rw [he]
    exact form_001011_pos
  · have he : (fun u v w : ℝ => form_00101 (u/2) (v/2) (u/2+v/2+w)) = form_001012 := by
      funext u v w; dsimp [form_00101, form_001012]; ring
    rw [he]
    exact form_001012_pos
  · have he : (fun u v w : ℝ => form_00101 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_001013 := by
      funext u v w; dsimp [form_00101, form_001013]; ring
    rw [he]
    exact form_001013_pos

private def form_00102 (u v w : ℝ) : ℝ :=
  (1789433809 / 32768 : ℝ)*u^3 + (5508073407 / 32768 : ℝ)*u^2*v^1 + (5538098139 / 16384 : ℝ)*u^2*w^1 + (2822143029 / 16384 : ℝ)*u^1*v^2 + (5643157569 / 8192 : ℝ)*u^1*v^1*w^1 + (5989340511 / 8192 : ℝ)*u^1*w^2 + (240699611 / 4096 : ℝ)*v^3 + (2872270191 / 8192 : ℝ)*v^2*w^1 + (6066370863 / 8192 : ℝ)*v^1*w^2 + (2219880565 / 4096 : ℝ)*w^3

private theorem form_00102_pos : ConePositive form_00102 := by
  intro u v w hu hv hw hs
  unfold form_00102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001030 (u v w : ℝ) : ℝ :=
  (1789433809 / 32768 : ℝ)*u^3 + (5168479983 / 65536 : ℝ)*u^2*v^1 + (5438187417 / 32768 : ℝ)*u^2*w^1 + (3114866025 / 65536 : ℝ)*u^1*v^2 + (10542597717 / 65536 : ℝ)*u^1*v^1*w^1 + (22028734299 / 131072 : ℝ)*u^1*w^2 + (95124053 / 8192 : ℝ)*v^3 + (6379010973 / 131072 : ℝ)*v^2*w^1 + (21492997467 / 262144 : ℝ)*v^1*w^2 + (7433695081 / 131072 : ℝ)*w^3

private theorem form_001030_pos : ConePositive form_001030 := by
  intro u v w hu hv hw hs
  unfold form_001030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001031 (u v w : ℝ) : ℝ :=
  (95124053 / 8192 : ℝ)*u^3 + (1451088519 / 65536 : ℝ)*u^2*v^1 + (4715233467 / 131072 : ℝ)*u^2*w^1 + (1840924971 / 65536 : ℝ)*u^1*v^2 + (2995097133 / 65536 : ℝ)*u^1*v^1*w^1 + (9725551311 / 262144 : ℝ)*u^1*w^2 + (48320955 / 8192 : ℝ)*v^3 + (1867979295 / 65536 : ℝ)*v^2*w^1 + (193006443 / 8192 : ℝ)*v^1*w^2 + (3339004501 / 262144 : ℝ)*w^3

private theorem form_001031_pos : ConePositive form_001031 := by
  intro u v w hu hv hw hs
  unfold form_001031
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001032 (u v w : ℝ) : ℝ :=
  (7433695081 / 131072 : ℝ)*u^3 + (22037699355 / 262144 : ℝ)*u^2*v^1 + (22573436187 / 131072 : ℝ)*u^2*w^1 + (6783179319 / 131072 : ℝ)*u^1*v^2 + (11219117007 / 65536 : ℝ)*u^1*v^1*w^1 + (5710538361 / 32768 : ℝ)*u^1*w^2 + (3339004501 / 262144 : ℝ)*v^3 + (6928910415 / 131072 : ℝ)*v^2*w^1 + (2854393311 / 32768 : ℝ)*v^1*w^2 + (240699611 / 4096 : ℝ)*w^3

private theorem form_001032_pos : ConePositive form_001032 := by
  intro u v w hu hv hw hs
  unfold form_001032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_001033 (u v w : ℝ) : ℝ :=
  (7433695081 / 131072 : ℝ)*u^3 + (21492997467 / 262144 : ℝ)*u^2*v^1 + (22037699355 / 262144 : ℝ)*u^2*w^1 + (6379010973 / 131072 : ℝ)*u^1*v^2 + (13165823979 / 131072 : ℝ)*u^1*v^1*w^1 + (6783179319 / 131072 : ℝ)*u^1*w^2 + (95124053 / 8192 : ℝ)*v^3 + (4715233467 / 131072 : ℝ)*v^2*w^1 + (9725551311 / 262144 : ℝ)*v^1*w^2 + (3339004501 / 262144 : ℝ)*w^3

private theorem form_001033_pos : ConePositive form_001033 := by
  intro u v w hu hv hw hs
  unfold form_001033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00103 (u v w : ℝ) : ℝ :=
  (1789433809 / 32768 : ℝ)*u^3 + (-49955361 / 8192 : ℝ)*u^2*v^1 + (5508073407 / 32768 : ℝ)*u^2*w^1 + (1261073511 / 32768 : ℝ)*u^1*v^2 + (-133955673 / 16384 : ℝ)*u^1*v^1*w^1 + (2822143029 / 16384 : ℝ)*u^1*w^2 + (48320955 / 8192 : ℝ)*v^3 + (1288127835 / 32768 : ℝ)*v^2*w^1 + (-34002021 / 16384 : ℝ)*v^1*w^2 + (240699611 / 4096 : ℝ)*w^3

private theorem form_00103_pos : ConePositive form_00103 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00103 (u+v/2+w/2) (v/2) (w/2)) = form_001030 := by
      funext u v w; dsimp [form_00103, form_001030]; ring
    rw [he]
    exact form_001030_pos
  · have he : (fun u v w : ℝ => form_00103 (u/2) (u/2+v+w/2) (w/2)) = form_001031 := by
      funext u v w; dsimp [form_00103, form_001031]; ring
    rw [he]
    exact form_001031_pos
  · have he : (fun u v w : ℝ => form_00103 (u/2) (v/2) (u/2+v/2+w)) = form_001032 := by
      funext u v w; dsimp [form_00103, form_001032]; ring
    rw [he]
    exact form_001032_pos
  · have he : (fun u v w : ℝ => form_00103 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_001033 := by
      funext u v w; dsimp [form_00103, form_001033]; ring
    rw [he]
    exact form_001033_pos

private def form_0010 (u v w : ℝ) : ℝ :=
  (649863 / 128 : ℝ)*u^3 + (4316895 / 256 : ℝ)*u^2*v^1 + (54764703 / 1024 : ℝ)*u^2*w^1 + (9483885 / 512 : ℝ)*u^1*v^2 + (123543945 / 1024 : ℝ)*u^1*v^1*w^1 + (-654591 / 4 : ℝ)*u^1*w^2 + (6886701 / 1024 : ℝ)*v^3 + (271440351 / 4096 : ℝ)*v^2*w^1 + (-37079427 / 256 : ℝ)*v^1*w^2 + (2219880565 / 4096 : ℝ)*w^3

private theorem form_0010_pos : ConePositive form_0010 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0010 (u+v/2+w/2) (v/2) (w/2)) = form_00100 := by
      funext u v w; dsimp [form_0010, form_00100]; ring
    rw [he]
    exact form_00100_pos
  · have he : (fun u v w : ℝ => form_0010 (u/2) (u/2+v+w/2) (w/2)) = form_00101 := by
      funext u v w; dsimp [form_0010, form_00101]; ring
    rw [he]
    exact form_00101_pos
  · have he : (fun u v w : ℝ => form_0010 (u/2) (v/2) (u/2+v/2+w)) = form_00102 := by
      funext u v w; dsimp [form_0010, form_00102]; ring
    rw [he]
    exact form_00102_pos
  · have he : (fun u v w : ℝ => form_0010 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00103 := by
      funext u v w; dsimp [form_0010, form_00103]; ring
    rw [he]
    exact form_00103_pos

private def form_00110 (u v w : ℝ) : ℝ :=
  (6886701 / 1024 : ℝ)*u^3 + (43012539 / 2048 : ℝ)*u^2*v^1 + (360850095 / 8192 : ℝ)*u^2*w^1 + (89401887 / 4096 : ℝ)*u^1*v^2 + (752790555 / 8192 : ℝ)*u^1*v^1*w^1 + (11807805 / 2048 : ℝ)*u^1*w^2 + (61834833 / 8192 : ℝ)*v^3 + (1563905079 / 32768 : ℝ)*v^2*w^1 + (39233085 / 4096 : ℝ)*v^1*w^2 + (2054343877 / 32768 : ℝ)*w^3

private theorem form_00110_pos : ConePositive form_00110 := by
  intro u v w hu hv hw hs
  unfold form_00110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00111 (u v w : ℝ) : ℝ :=
  (61834833 / 8192 : ℝ)*u^3 + (24025653 / 1024 : ℝ)*u^2*v^1 + (1590707979 / 32768 : ℝ)*u^2*w^1 + (3107079 / 128 : ℝ)*u^1*v^2 + (206102547 / 2048 : ℝ)*u^1*v^1*w^1 + (215150523 / 16384 : ℝ)*u^1*w^2 + (133731 / 16 : ℝ)*v^3 + (26608239 / 512 : ℝ)*v^2*w^1 + (34211163 / 2048 : ℝ)*v^1*w^2 + (33990271 / 512 : ℝ)*w^3

private theorem form_00111_pos : ConePositive form_00111 := by
  intro u v w hu hv hw hs
  unfold form_00111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00112 (u v w : ℝ) : ℝ :=
  (2054343877 / 32768 : ℝ)*u^3 + (6287971431 / 32768 : ℝ)*u^2*v^1 + (6068569191 / 16384 : ℝ)*u^2*w^1 + (3204527235 / 16384 : ℝ)*u^1*v^2 + (3081209313 / 4096 : ℝ)*u^1*v^1*w^1 + (3167478423 / 4096 : ℝ)*u^1*w^2 + (33990271 / 512 : ℝ)*v^3 + (781555341 / 2048 : ℝ)*v^2*w^1 + (50035041 / 64 : ℝ)*v^1*w^2 + (286648091 / 512 : ℝ)*w^3

private theorem form_00112_pos : ConePositive form_00112 := by
  intro u v w hu hv hw hs
  unfold form_00112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00113 (u v w : ℝ) : ℝ :=
  (2054343877 / 32768 : ℝ)*u^3 + (39233085 / 4096 : ℝ)*u^2*v^1 + (6287971431 / 32768 : ℝ)*u^2*w^1 + (1563905079 / 32768 : ℝ)*u^1*v^2 + (372188649 / 16384 : ℝ)*u^1*v^1*w^1 + (3204527235 / 16384 : ℝ)*u^1*w^2 + (61834833 / 8192 : ℝ)*v^3 + (1590707979 / 32768 : ℝ)*v^2*w^1 + (215150523 / 16384 : ℝ)*v^1*w^2 + (33990271 / 512 : ℝ)*w^3

private theorem form_00113_pos : ConePositive form_00113 := by
  intro u v w hu hv hw hs
  unfold form_00113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0011 (u v w : ℝ) : ℝ :=
  (6886701 / 1024 : ℝ)*u^3 + (5588109 / 256 : ℝ)*u^2*v^1 + (278209683 / 4096 : ℝ)*u^2*w^1 + (1502307 / 64 : ℝ)*u^1*v^2 + (75632679 / 512 : ℝ)*u^1*v^1*w^1 + (-272298669 / 2048 : ℝ)*u^1*w^2 + (133731 / 16 : ℝ)*v^3 + (20189151 / 256 : ℝ)*v^2*w^1 + (-59383617 / 512 : ℝ)*v^1*w^2 + (286648091 / 512 : ℝ)*w^3

private theorem form_0011_pos : ConePositive form_0011 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0011 (u+v/2+w/2) (v/2) (w/2)) = form_00110 := by
      funext u v w; dsimp [form_0011, form_00110]; ring
    rw [he]
    exact form_00110_pos
  · have he : (fun u v w : ℝ => form_0011 (u/2) (u/2+v+w/2) (w/2)) = form_00111 := by
      funext u v w; dsimp [form_0011, form_00111]; ring
    rw [he]
    exact form_00111_pos
  · have he : (fun u v w : ℝ => form_0011 (u/2) (v/2) (u/2+v/2+w)) = form_00112 := by
      funext u v w; dsimp [form_0011, form_00112]; ring
    rw [he]
    exact form_00112_pos
  · have he : (fun u v w : ℝ => form_0011 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00113 := by
      funext u v w; dsimp [form_0011, form_00113]; ring
    rw [he]
    exact form_00113_pos

private def form_0012 (u v w : ℝ) : ℝ :=
  (2219880565 / 4096 : ℝ)*u^3 + (6736672047 / 4096 : ℝ)*u^2*v^1 + (6994792287 / 2048 : ℝ)*u^2*w^1 + (3405012891 / 2048 : ℝ)*u^1*v^2 + (1764452025 / 256 : ℝ)*u^1*v^1*w^1 + (3692353791 / 512 : ℝ)*u^1*w^2 + (286648091 / 512 : ℝ)*v^3 + (1779272163 / 512 : ℝ)*v^2*w^1 + (1858844931 / 256 : ℝ)*v^1*w^2 + (325899551 / 64 : ℝ)*w^3

private theorem form_0012_pos : ConePositive form_0012 := by
  intro u v w hu hv hw hs
  unfold form_0012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00130 (u v w : ℝ) : ℝ :=
  (2219880565 / 4096 : ℝ)*u^3 + (6066370863 / 8192 : ℝ)*u^2*v^1 + (6698156871 / 4096 : ℝ)*u^2*w^1 + (2872270191 / 8192 : ℝ)*u^1*v^2 + (12234124539 / 8192 : ℝ)*u^1*v^1*w^1 + (26943011571 / 16384 : ℝ)*u^1*w^2 + (240699611 / 4096 : ℝ)*v^3 + (5810792685 / 16384 : ℝ)*v^2*w^1 + (24667306659 / 32768 : ℝ)*v^1*w^2 + (9029881561 / 16384 : ℝ)*w^3

private theorem form_00130_pos : ConePositive form_00130 := by
  intro u v w hu hv hw hs
  unfold form_00130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00131 (u v w : ℝ) : ℝ :=
  (240699611 / 4096 : ℝ)*u^3 + (16125141 / 8192 : ℝ)*u^2*v^1 + (2954647635 / 16384 : ℝ)*u^2*w^1 + (354080763 / 8192 : ℝ)*u^1*v^2 + (63372075 / 8192 : ℝ)*u^1*v^1*w^1 + (6038091831 / 32768 : ℝ)*u^1*w^2 + (6886701 / 1024 : ℝ)*v^3 + (360850095 / 8192 : ℝ)*v^2*w^1 + (11807805 / 2048 : ℝ)*v^1*w^2 + (2054343877 / 32768 : ℝ)*w^3

private theorem form_00131_pos : ConePositive form_00131 := by
  intro u v w hu hv hw hs
  unfold form_00131
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00132 (u v w : ℝ) : ℝ :=
  (9029881561 / 16384 : ℝ)*u^3 + (24960572883 / 32768 : ℝ)*u^2*v^1 + (27236277795 / 16384 : ℝ)*u^2*w^1 + (6006099291 / 16384 : ℝ)*u^1*v^2 + (12576064257 / 8192 : ℝ)*u^1*v^1*w^1 + (6844789983 / 4096 : ℝ)*u^1*w^2 + (2054343877 / 32768 : ℝ)*v^3 + (6068569191 / 16384 : ℝ)*v^2*w^1 + (3167478423 / 4096 : ℝ)*v^1*w^2 + (286648091 / 512 : ℝ)*w^3

private theorem form_00132_pos : ConePositive form_00132 := by
  intro u v w hu hv hw hs
  unfold form_00132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00133 (u v w : ℝ) : ℝ :=
  (9029881561 / 16384 : ℝ)*u^3 + (24667306659 / 32768 : ℝ)*u^2*v^1 + (24960572883 / 32768 : ℝ)*u^2*w^1 + (5810792685 / 16384 : ℝ)*u^1*v^2 + (11820642951 / 16384 : ℝ)*u^1*v^1*w^1 + (6006099291 / 16384 : ℝ)*u^1*w^2 + (240699611 / 4096 : ℝ)*v^3 + (2954647635 / 16384 : ℝ)*v^2*w^1 + (6038091831 / 32768 : ℝ)*v^1*w^2 + (2054343877 / 32768 : ℝ)*w^3

private theorem form_00133_pos : ConePositive form_00133 := by
  intro u v w hu hv hw hs
  unfold form_00133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0013 (u v w : ℝ) : ℝ :=
  (2219880565 / 4096 : ℝ)*u^3 + (-37079427 / 256 : ℝ)*u^2*v^1 + (6736672047 / 4096 : ℝ)*u^2*w^1 + (271440351 / 4096 : ℝ)*u^1*v^2 + (-568918371 / 2048 : ℝ)*u^1*v^1*w^1 + (3405012891 / 2048 : ℝ)*u^1*w^2 + (6886701 / 1024 : ℝ)*v^3 + (278209683 / 4096 : ℝ)*v^2*w^1 + (-272298669 / 2048 : ℝ)*v^1*w^2 + (286648091 / 512 : ℝ)*w^3

private theorem form_0013_pos : ConePositive form_0013 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0013 (u+v/2+w/2) (v/2) (w/2)) = form_00130 := by
      funext u v w; dsimp [form_0013, form_00130]; ring
    rw [he]
    exact form_00130_pos
  · have he : (fun u v w : ℝ => form_0013 (u/2) (u/2+v+w/2) (w/2)) = form_00131 := by
      funext u v w; dsimp [form_0013, form_00131]; ring
    rw [he]
    exact form_00131_pos
  · have he : (fun u v w : ℝ => form_0013 (u/2) (v/2) (u/2+v/2+w)) = form_00132 := by
      funext u v w; dsimp [form_0013, form_00132]; ring
    rw [he]
    exact form_00132_pos
  · have he : (fun u v w : ℝ => form_0013 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00133 := by
      funext u v w; dsimp [form_0013, form_00133]; ring
    rw [he]
    exact form_00133_pos

private def form_001 (u v w : ℝ) : ℝ :=
  (649863 / 128 : ℝ)*u^3 + (1183653 / 64 : ℝ)*u^2*v^1 + (46966347 / 512 : ℝ)*u^2*w^1 + (699921 / 32 : ℝ)*u^1*v^2 + (29655009 / 128 : ℝ)*u^1*v^1*w^1 + (-218440821 / 256 : ℝ)*u^1*w^2 + (133731 / 16 : ℝ)*v^3 + (16979607 / 128 : ℝ)*v^2*w^1 + (-96552375 / 128 : ℝ)*v^1*w^2 + (325899551 / 64 : ℝ)*w^3

private theorem form_001_pos : ConePositive form_001 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_001 (u+v/2+w/2) (v/2) (w/2)) = form_0010 := by
      funext u v w; dsimp [form_001, form_0010]; ring
    rw [he]
    exact form_0010_pos
  · have he : (fun u v w : ℝ => form_001 (u/2) (u/2+v+w/2) (w/2)) = form_0011 := by
      funext u v w; dsimp [form_001, form_0011]; ring
    rw [he]
    exact form_0011_pos
  · have he : (fun u v w : ℝ => form_001 (u/2) (v/2) (u/2+v/2+w)) = form_0012 := by
      funext u v w; dsimp [form_001, form_0012]; ring
    rw [he]
    exact form_0012_pos
  · have he : (fun u v w : ℝ => form_001 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0013 := by
      funext u v w; dsimp [form_001, form_0013]; ring
    rw [he]
    exact form_0013_pos

private def form_002 (u v w : ℝ) : ℝ :=
  (2552838577 / 512 : ℝ)*u^3 + (7716509679 / 512 : ℝ)*u^2*v^1 + (7918267875 / 256 : ℝ)*u^2*w^1 + (3885458541 / 256 : ℝ)*u^1*v^2 + (7968326037 / 128 : ℝ)*u^1*v^1*w^1 + (8182304739 / 128 : ℝ)*u^1*w^2 + (325899551 / 64 : ℝ)*v^3 + (4007346987 / 128 : ℝ)*v^2*w^1 + (8224778331 / 128 : ℝ)*v^1*w^2 + (2816745841 / 64 : ℝ)*w^3

private theorem form_002_pos : ConePositive form_002 := by
  intro u v w hu hv hw hs
  unfold form_002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0030 (u v w : ℝ) : ℝ :=
  (2552838577 / 512 : ℝ)*u^3 + (7197005391 / 1024 : ℝ)*u^2*v^1 + (7687512705 / 512 : ℝ)*u^2*w^1 + (3390395265 / 1024 : ℝ)*u^1*v^2 + (14464289757 / 1024 : ℝ)*u^1*v^1*w^1 + (30862452171 / 2048 : ℝ)*u^1*w^2 + (16712681 / 32 : ℝ)*v^3 + (6822907965 / 2048 : ℝ)*v^2*w^1 + (29065609563 / 4096 : ℝ)*v^1*w^2 + (10323730873 / 2048 : ℝ)*w^3

private theorem form_0030_pos : ConePositive form_0030 := by
  intro u v w hu hv hw hs
  unfold form_0030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00310 (u v w : ℝ) : ℝ :=
  (16712681 / 32 : ℝ)*u^3 + (1422856863 / 2048 : ℝ)*u^2*v^1 + (6459786939 / 4096 : ℝ)*u^2*w^1 + (1294390185 / 4096 : ℝ)*u^1*v^2 + (2873750391 / 2048 : ℝ)*u^1*v^1*w^1 + (26004089595 / 16384 : ℝ)*u^1*w^2 + (205769009 / 4096 : ℝ)*v^3 + (5250931701 / 16384 : ℝ)*v^2*w^1 + (23210885835 / 32768 : ℝ)*v^1*w^2 + (8721809725 / 16384 : ℝ)*w^3

private theorem form_00310_pos : ConePositive form_00310 := by
  intro u v w hu hv hw hs
  unfold form_00310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_003110 (u v w : ℝ) : ℝ :=
  (205769009 / 4096 : ℝ)*u^3 + (34845681 / 512 : ℝ)*u^2*v^1 + (5011827177 / 32768 : ℝ)*u^2*w^1 + (635135859 / 16384 : ℝ)*u^1*v^2 + (4568213391 / 32768 : ℝ)*u^1*v^1*w^1 + (20337381939 / 131072 : ℝ)*u^1*w^2 + (76042397 / 8192 : ℝ)*v^3 + (5237015301 / 131072 : ℝ)*v^2*w^1 + (18701542419 / 262144 : ℝ)*v^1*w^2 + (6874656733 / 131072 : ℝ)*w^3

private theorem form_003110_pos : ConePositive form_003110 := by
  intro u v w hu hv hw hs
  unfold form_003110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_003111 (u v w : ℝ) : ℝ :=
  (76042397 / 8192 : ℝ)*u^3 + (277372905 / 16384 : ℝ)*u^2*v^1 + (3805963485 / 131072 : ℝ)*u^2*w^1 + (99883971 / 4096 : ℝ)*u^1*v^2 + (578726913 / 16384 : ℝ)*u^1*v^1*w^1 + (7920607791 / 262144 : ℝ)*u^1*w^2 + (649863 / 128 : ℝ)*v^3 + (101554839 / 4096 : ℝ)*v^2*w^1 + (150691665 / 8192 : ℝ)*v^1*w^2 + (2741987953 / 262144 : ℝ)*w^3

private theorem form_003111_pos : ConePositive form_003111 := by
  intro u v w hu hv hw hs
  unfold form_003111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_003112 (u v w : ℝ) : ℝ :=
  (6874656733 / 131072 : ℝ)*u^3 + (19274718939 / 262144 : ℝ)*u^2*v^1 + (20910558459 / 131072 : ℝ)*u^2*w^1 + (5662219185 / 131072 : ℝ)*u^1*v^2 + (4924109463 / 32768 : ℝ)*u^1*v^1*w^1 + (5298415437 / 32768 : ℝ)*u^1*w^2 + (2741987953 / 262144 : ℝ)*v^3 + (5814897219 / 131072 : ℝ)*v^2*w^1 + (5028708003 / 65536 : ℝ)*v^1*w^2 + (1789433809 / 32768 : ℝ)*w^3

private theorem form_003112_pos : ConePositive form_003112 := by
  intro u v w hu hv hw hs
  unfold form_003112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_003113 (u v w : ℝ) : ℝ :=
  (6874656733 / 131072 : ℝ)*u^3 + (18701542419 / 262144 : ℝ)*u^2*v^1 + (19274718939 / 262144 : ℝ)*u^2*w^1 + (5237015301 / 131072 : ℝ)*u^1*v^2 + (10902719457 / 131072 : ℝ)*u^1*v^1*w^1 + (5662219185 / 131072 : ℝ)*u^1*w^2 + (76042397 / 8192 : ℝ)*v^3 + (3805963485 / 131072 : ℝ)*v^2*w^1 + (7920607791 / 262144 : ℝ)*v^1*w^2 + (2741987953 / 262144 : ℝ)*w^3

private theorem form_003113_pos : ConePositive form_003113 := by
  intro u v w hu hv hw hs
  unfold form_003113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00311 (u v w : ℝ) : ℝ :=
  (205769009 / 4096 : ℝ)*u^3 + (-59776131 / 4096 : ℝ)*u^2*v^1 + (2542599069 / 16384 : ℝ)*u^2*w^1 + (68690547 / 2048 : ℝ)*u^1*v^2 + (-102254631 / 4096 : ℝ)*u^1*v^1*w^1 + (5228529447 / 32768 : ℝ)*u^1*w^2 + (649863 / 128 : ℝ)*v^3 + (70361415 / 2048 : ℝ)*v^2*w^1 + (-21224589 / 2048 : ℝ)*v^1*w^2 + (1789433809 / 32768 : ℝ)*w^3

private theorem form_00311_pos : ConePositive form_00311 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00311 (u+v/2+w/2) (v/2) (w/2)) = form_003110 := by
      funext u v w; dsimp [form_00311, form_003110]; ring
    rw [he]
    exact form_003110_pos
  · have he : (fun u v w : ℝ => form_00311 (u/2) (u/2+v+w/2) (w/2)) = form_003111 := by
      funext u v w; dsimp [form_00311, form_003111]; ring
    rw [he]
    exact form_003111_pos
  · have he : (fun u v w : ℝ => form_00311 (u/2) (v/2) (u/2+v/2+w)) = form_003112 := by
      funext u v w; dsimp [form_00311, form_003112]; ring
    rw [he]
    exact form_003112_pos
  · have he : (fun u v w : ℝ => form_00311 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_003113 := by
      funext u v w; dsimp [form_00311, form_003113]; ring
    rw [he]
    exact form_003113_pos

private def form_00312 (u v w : ℝ) : ℝ :=
  (8721809725 / 16384 : ℝ)*u^3 + (23533564995 / 32768 : ℝ)*u^2*v^1 + (26326768755 / 16384 : ℝ)*u^2*w^1 + (5468212149 / 16384 : ℝ)*u^1*v^2 + (1484202699 / 1024 : ℝ)*u^1*v^1*w^1 + (6621126519 / 4096 : ℝ)*u^1*w^2 + (1789433809 / 32768 : ℝ)*v^3 + (5538098139 / 16384 : ℝ)*v^2*w^1 + (5989340511 / 8192 : ℝ)*v^1*w^2 + (2219880565 / 4096 : ℝ)*w^3

private theorem form_00312_pos : ConePositive form_00312 := by
  intro u v w hu hv hw hs
  unfold form_00312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_00313 (u v w : ℝ) : ℝ :=
  (8721809725 / 16384 : ℝ)*u^3 + (23210885835 / 32768 : ℝ)*u^2*v^1 + (23533564995 / 32768 : ℝ)*u^2*w^1 + (5250931701 / 16384 : ℝ)*u^1*v^2 + (10722746109 / 16384 : ℝ)*u^1*v^1*w^1 + (5468212149 / 16384 : ℝ)*u^1*w^2 + (205769009 / 4096 : ℝ)*v^3 + (2542599069 / 16384 : ℝ)*v^2*w^1 + (5228529447 / 32768 : ℝ)*v^1*w^2 + (1789433809 / 32768 : ℝ)*w^3

private theorem form_00313_pos : ConePositive form_00313 := by
  intro u v w hu hv hw hs
  unfold form_00313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0031 (u v w : ℝ) : ℝ :=
  (16712681 / 32 : ℝ)*u^3 + (-181560513 / 1024 : ℝ)*u^2*v^1 + (3250952187 / 2048 : ℝ)*u^2*w^1 + (53093835 / 1024 : ℝ)*u^1*v^2 + (-349165131 / 1024 : ℝ)*u^1*v^1*w^1 + (6582611343 / 4096 : ℝ)*u^1*w^2 + (649863 / 128 : ℝ)*v^3 + (54764703 / 1024 : ℝ)*v^2*w^1 + (-654591 / 4 : ℝ)*v^1*w^2 + (2219880565 / 4096 : ℝ)*w^3

private theorem form_0031_pos : ConePositive form_0031 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0031 (u+v/2+w/2) (v/2) (w/2)) = form_00310 := by
      funext u v w; dsimp [form_0031, form_00310]; ring
    rw [he]
    exact form_00310_pos
  · have he : (fun u v w : ℝ => form_0031 (u/2) (u/2+v+w/2) (w/2)) = form_00311 := by
      funext u v w; dsimp [form_0031, form_00311]; ring
    rw [he]
    exact form_00311_pos
  · have he : (fun u v w : ℝ => form_0031 (u/2) (v/2) (u/2+v/2+w)) = form_00312 := by
      funext u v w; dsimp [form_0031, form_00312]; ring
    rw [he]
    exact form_00312_pos
  · have he : (fun u v w : ℝ => form_0031 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_00313 := by
      funext u v w; dsimp [form_0031, form_00313]; ring
    rw [he]
    exact form_00313_pos

private def form_0032 (u v w : ℝ) : ℝ :=
  (10323730873 / 2048 : ℝ)*u^3 + (29283090459 / 4096 : ℝ)*u^2*v^1 + (31079933067 / 2048 : ℝ)*u^2*w^1 + (6956277111 / 2048 : ℝ)*u^1*v^2 + (14706399351 / 1024 : ℝ)*u^1*v^1*w^1 + (7796253153 / 512 : ℝ)*u^1*w^2 + (2219880565 / 4096 : ℝ)*v^3 + (6994792287 / 2048 : ℝ)*v^2*w^1 + (3692353791 / 512 : ℝ)*v^1*w^2 + (325899551 / 64 : ℝ)*w^3

private theorem form_0032_pos : ConePositive form_0032 := by
  intro u v w hu hv hw hs
  unfold form_0032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0033 (u v w : ℝ) : ℝ :=
  (10323730873 / 2048 : ℝ)*u^3 + (29065609563 / 4096 : ℝ)*u^2*v^1 + (29283090459 / 4096 : ℝ)*u^2*w^1 + (6822907965 / 2048 : ℝ)*u^1*v^2 + (13782845979 / 2048 : ℝ)*u^1*v^1*w^1 + (6956277111 / 2048 : ℝ)*u^1*w^2 + (16712681 / 32 : ℝ)*v^3 + (3250952187 / 2048 : ℝ)*v^2*w^1 + (6582611343 / 4096 : ℝ)*v^1*w^2 + (2219880565 / 4096 : ℝ)*w^3

private theorem form_0033_pos : ConePositive form_0033 := by
  intro u v w hu hv hw hs
  unfold form_0033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_003 (u v w : ℝ) : ℝ :=
  (2552838577 / 512 : ℝ)*u^3 + (-115377585 / 128 : ℝ)*u^2*v^1 + (7716509679 / 512 : ℝ)*u^2*w^1 + (45295479 / 512 : ℝ)*u^1*v^2 + (-449225313 / 256 : ℝ)*u^1*v^1*w^1 + (3885458541 / 256 : ℝ)*u^1*w^2 + (649863 / 128 : ℝ)*v^3 + (46966347 / 512 : ℝ)*v^2*w^1 + (-218440821 / 256 : ℝ)*v^1*w^2 + (325899551 / 64 : ℝ)*w^3

private theorem form_003_pos : ConePositive form_003 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_003 (u+v/2+w/2) (v/2) (w/2)) = form_0030 := by
      funext u v w; dsimp [form_003, form_0030]; ring
    rw [he]
    exact form_0030_pos
  · have he : (fun u v w : ℝ => form_003 (u/2) (u/2+v+w/2) (w/2)) = form_0031 := by
      funext u v w; dsimp [form_003, form_0031]; ring
    rw [he]
    exact form_0031_pos
  · have he : (fun u v w : ℝ => form_003 (u/2) (v/2) (u/2+v/2+w)) = form_0032 := by
      funext u v w; dsimp [form_003, form_0032]; ring
    rw [he]
    exact form_0032_pos
  · have he : (fun u v w : ℝ => form_003 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0033 := by
      funext u v w; dsimp [form_003, form_0033]; ring
    rw [he]
    exact form_0033_pos

private def form_00 (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (46251 / 4 : ℝ)*u^2*v^1 + (243495 / 4 : ℝ)*u^2*w^1 + (37341 / 2 : ℝ)*u^1*v^2 + (5740245 / 16 : ℝ)*u^1*v^1*w^1 + (-16745799 / 4 : ℝ)*u^1*w^2 + (133731 / 16 : ℝ)*v^3 + (15374835 / 64 : ℝ)*v^2*w^1 + (-28182399 / 8 : ℝ)*v^1*w^2 + (2816745841 / 64 : ℝ)*w^3

private theorem form_00_pos : ConePositive form_00 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_00 (u+v/2+w/2) (v/2) (w/2)) = form_000 := by
      funext u v w; dsimp [form_00, form_000]; ring
    rw [he]
    exact form_000_pos
  · have he : (fun u v w : ℝ => form_00 (u/2) (u/2+v+w/2) (w/2)) = form_001 := by
      funext u v w; dsimp [form_00, form_001]; ring
    rw [he]
    exact form_001_pos
  · have he : (fun u v w : ℝ => form_00 (u/2) (v/2) (u/2+v/2+w)) = form_002 := by
      funext u v w; dsimp [form_00, form_002]; ring
    rw [he]
    exact form_002_pos
  · have he : (fun u v w : ℝ => form_00 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_003 := by
      funext u v w; dsimp [form_00, form_003]; ring
    rw [he]
    exact form_003_pos

private def form_01000 (u v w : ℝ) : ℝ :=
  (133731 / 16 : ℝ)*u^3 + (3312009 / 128 : ℝ)*u^2*v^1 + (27018099 / 512 : ℝ)*u^2*w^1 + (27304533 / 1024 : ℝ)*u^1*v^2 + (222863121 / 2048 : ℝ)*u^1*v^1*w^1 + (20476005 / 1024 : ℝ)*u^1*w^2 + (74925567 / 8192 : ℝ)*v^3 + (1832497407 / 32768 : ℝ)*v^2*w^1 + (191037513 / 8192 : ℝ)*v^1*w^2 + (2288399857 / 32768 : ℝ)*w^3

private theorem form_01000_pos : ConePositive form_01000 := by
  intro u v w hu hv hw hs
  unfold form_01000
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01001 (u v w : ℝ) : ℝ :=
  (74925567 / 8192 : ℝ)*u^3 + (115558569 / 4096 : ℝ)*u^2*v^1 + (1857859155 / 32768 : ℝ)*u^2*w^1 + (59332581 / 2048 : ℝ)*u^1*v^2 + (953471295 / 8192 : ℝ)*u^1*v^1*w^1 + (431412963 / 16384 : ℝ)*u^1*w^2 + (10140795 / 1024 : ℝ)*v^3 + (487930779 / 8192 : ℝ)*v^2*w^1 + (240821679 / 8192 : ℝ)*v^1*w^2 + (18696203 / 256 : ℝ)*w^3

private theorem form_01001_pos : ConePositive form_01001 := by
  intro u v w hu hv hw hs
  unfold form_01001
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01002 (u v w : ℝ) : ℝ :=
  (2288399857 / 32768 : ℝ)*u^3 + (6974117463 / 32768 : ℝ)*u^2*v^1 + (6537583491 / 16384 : ℝ)*u^2*w^1 + (3539440581 / 16384 : ℝ)*u^1*v^2 + (6619628067 / 8192 : ℝ)*u^1*v^1*w^1 + (6642256995 / 8192 : ℝ)*u^1*w^2 + (18696203 / 256 : ℝ)*v^3 + (3348849297 / 8192 : ℝ)*v^2*w^1 + (6703986015 / 8192 : ℝ)*v^1*w^2 + (2358838225 / 4096 : ℝ)*w^3

private theorem form_01002_pos : ConePositive form_01002 := by
  intro u v w hu hv hw hs
  unfold form_01002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01003 (u v w : ℝ) : ℝ :=
  (2288399857 / 32768 : ℝ)*u^3 + (191037513 / 8192 : ℝ)*u^2*v^1 + (6974117463 / 32768 : ℝ)*u^2*w^1 + (1832497407 / 32768 : ℝ)*u^1*v^2 + (813742491 / 16384 : ℝ)*u^1*v^1*w^1 + (3539440581 / 16384 : ℝ)*u^1*w^2 + (74925567 / 8192 : ℝ)*v^3 + (1857859155 / 32768 : ℝ)*v^2*w^1 + (431412963 / 16384 : ℝ)*v^1*w^2 + (18696203 / 256 : ℝ)*w^3

private theorem form_01003_pos : ConePositive form_01003 := by
  intro u v w hu hv hw hs
  unfold form_01003
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0100 (u v w : ℝ) : ℝ :=
  (133731 / 16 : ℝ)*u^3 + (1707237 / 64 : ℝ)*u^2*v^1 + (20599011 / 256 : ℝ)*u^2*w^1 + (7227549 / 256 : ℝ)*u^1*v^2 + (87474933 / 512 : ℝ)*u^1*v^1*w^1 + (-27141105 / 256 : ℝ)*u^1*w^2 + (10140795 / 1024 : ℝ)*v^3 + (366241239 / 4096 : ℝ)*v^2*w^1 + (-93132165 / 1024 : ℝ)*v^1*w^2 + (2358838225 / 4096 : ℝ)*w^3

private theorem form_0100_pos : ConePositive form_0100 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0100 (u+v/2+w/2) (v/2) (w/2)) = form_01000 := by
      funext u v w; dsimp [form_0100, form_01000]; ring
    rw [he]
    exact form_01000_pos
  · have he : (fun u v w : ℝ => form_0100 (u/2) (u/2+v+w/2) (w/2)) = form_01001 := by
      funext u v w; dsimp [form_0100, form_01001]; ring
    rw [he]
    exact form_01001_pos
  · have he : (fun u v w : ℝ => form_0100 (u/2) (v/2) (u/2+v/2+w)) = form_01002 := by
      funext u v w; dsimp [form_0100, form_01002]; ring
    rw [he]
    exact form_01002_pos
  · have he : (fun u v w : ℝ => form_0100 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_01003 := by
      funext u v w; dsimp [form_0100, form_01003]; ring
    rw [he]
    exact form_01003_pos

private def form_01010 (u v w : ℝ) : ℝ :=
  (10140795 / 1024 : ℝ)*u^3 + (62356959 / 2048 : ℝ)*u^2*v^1 + (493979535 / 8192 : ℝ)*u^2*w^1 + (127656081 / 4096 : ℝ)*u^1*v^2 + (1010020473 / 8192 : ℝ)*u^1*v^1*w^1 + (32880939 / 1024 : ℝ)*u^1*w^2 + (86998293 / 8192 : ℝ)*v^3 + (2059712127 / 32768 : ℝ)*v^2*w^1 + (71493519 / 2048 : ℝ)*v^1*w^2 + (2489222293 / 32768 : ℝ)*w^3

private theorem form_01010_pos : ConePositive form_01010 := by
  intro u v w hu hv hw hs
  unfold form_01010
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01011 (u v w : ℝ) : ℝ :=
  (86998293 / 8192 : ℝ)*u^3 + (66669399 / 2048 : ℝ)*u^2*v^1 + (2082442995 / 32768 : ℝ)*u^2*w^1 + (17009919 / 512 : ℝ)*u^1*v^2 + (530326935 / 4096 : ℝ)*u^1*v^1*w^1 + (611216115 / 16384 : ℝ)*u^1*w^2 + (1444797 / 128 : ℝ)*v^3 + (134723259 / 2048 : ℝ)*v^2*w^1 + (163135815 / 4096 : ℝ)*v^1*w^2 + (322053419 / 4096 : ℝ)*w^3

private theorem form_01011_pos : ConePositive form_01011 := by
  intro u v w hu hv hw hs
  unfold form_01011
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01012 (u v w : ℝ) : ℝ :=
  (2489222293 / 32768 : ℝ)*u^3 + (7559373135 / 32768 : ℝ)*u^2*v^1 + (6941571855 / 16384 : ℝ)*u^2*w^1 + (3823313883 / 16384 : ℝ)*u^1*v^2 + (1752804177 / 2048 : ℝ)*u^1*v^1*w^1 + (3454728183 / 4096 : ℝ)*u^1*w^2 + (322053419 / 4096 : ℝ)*v^3 + (1769184699 / 4096 : ℝ)*v^2*w^1 + (1740772143 / 2048 : ℝ)*v^1*w^2 + (302067953 / 512 : ℝ)*w^3

private theorem form_01012_pos : ConePositive form_01012 := by
  intro u v w hu hv hw hs
  unfold form_01012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01013 (u v w : ℝ) : ℝ :=
  (2489222293 / 32768 : ℝ)*u^3 + (71493519 / 2048 : ℝ)*u^2*v^1 + (7559373135 / 32768 : ℝ)*u^2*w^1 + (2059712127 / 32768 : ℝ)*u^1*v^2 + (1183567485 / 16384 : ℝ)*u^1*v^1*w^1 + (3823313883 / 16384 : ℝ)*u^1*w^2 + (86998293 / 8192 : ℝ)*v^3 + (2082442995 / 32768 : ℝ)*v^2*w^1 + (611216115 / 16384 : ℝ)*v^1*w^2 + (322053419 / 4096 : ℝ)*w^3

private theorem form_01013_pos : ConePositive form_01013 := by
  intro u v w hu hv hw hs
  unfold form_01013
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0101 (u v w : ℝ) : ℝ :=
  (10140795 / 1024 : ℝ)*u^3 + (15967287 / 512 : ℝ)*u^2*v^1 + (372289995 / 4096 : ℝ)*u^2*w^1 + (8341137 / 256 : ℝ)*u^1*v^2 + (194151321 / 1024 : ℝ)*u^1*v^1*w^1 + (-170087253 / 2048 : ℝ)*u^1*w^2 + (1444797 / 128 : ℝ)*v^3 + (100048131 / 1024 : ℝ)*v^2*w^1 + (-71635575 / 1024 : ℝ)*v^1*w^2 + (302067953 / 512 : ℝ)*w^3

private theorem form_0101_pos : ConePositive form_0101 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0101 (u+v/2+w/2) (v/2) (w/2)) = form_01010 := by
      funext u v w; dsimp [form_0101, form_01010]; ring
    rw [he]
    exact form_01010_pos
  · have he : (fun u v w : ℝ => form_0101 (u/2) (u/2+v+w/2) (w/2)) = form_01011 := by
      funext u v w; dsimp [form_0101, form_01011]; ring
    rw [he]
    exact form_01011_pos
  · have he : (fun u v w : ℝ => form_0101 (u/2) (v/2) (u/2+v/2+w)) = form_01012 := by
      funext u v w; dsimp [form_0101, form_01012]; ring
    rw [he]
    exact form_01012_pos
  · have he : (fun u v w : ℝ => form_0101 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_01013 := by
      funext u v w; dsimp [form_0101, form_01013]; ring
    rw [he]
    exact form_01013_pos

private def form_0102 (u v w : ℝ) : ℝ :=
  (2358838225 / 4096 : ℝ)*u^3 + (7138243695 / 4096 : ℝ)*u^2*v^1 + (7293643515 / 2048 : ℝ)*u^2*w^1 + (3597999333 / 2048 : ℝ)*u^1*v^2 + (7345214757 / 1024 : ℝ)*u^1*v^1*w^1 + (7593168399 / 1024 : ℝ)*u^1*w^2 + (302067953 / 512 : ℝ)*v^3 + (3696451011 / 1024 : ℝ)*v^2*w^1 + (7636221303 / 1024 : ℝ)*v^1*w^2 + (2654083717 / 512 : ℝ)*w^3

private theorem form_0102_pos : ConePositive form_0102 := by
  intro u v w hu hv hw hs
  unfold form_0102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01030 (u v w : ℝ) : ℝ :=
  (2358838225 / 4096 : ℝ)*u^3 + (6703986015 / 8192 : ℝ)*u^2*v^1 + (7107379185 / 4096 : ℝ)*u^2*w^1 + (3348849297 / 8192 : ℝ)*u^1*v^2 + (13486042557 / 8192 : ℝ)*u^1*v^1*w^1 + (28549000731 / 16384 : ℝ)*u^1*w^2 + (18696203 / 256 : ℝ)*v^3 + (6747928989 / 16384 : ℝ)*v^2*w^1 + (27123923259 / 32768 : ℝ)*v^1*w^2 + (9554812105 / 16384 : ℝ)*w^3

private theorem form_01030_pos : ConePositive form_01030 := by
  intro u v w hu hv hw hs
  unfold form_01030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01031 (u v w : ℝ) : ℝ :=
  (18696203 / 256 : ℝ)*u^3 + (240821679 / 8192 : ℝ)*u^2*v^1 + (3639901371 / 16384 : ℝ)*u^2*w^1 + (487930779 / 8192 : ℝ)*u^1*v^2 + (504033621 / 8192 : ℝ)*u^1*v^1*w^1 + (7375960623 / 32768 : ℝ)*u^1*w^2 + (10140795 / 1024 : ℝ)*v^3 + (493979535 / 8192 : ℝ)*v^2*w^1 + (32880939 / 1024 : ℝ)*v^1*w^2 + (2489222293 / 32768 : ℝ)*w^3

private theorem form_01031_pos : ConePositive form_01031 := by
  intro u v w hu hv hw hs
  unfold form_01031
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01032 (u v w : ℝ) : ℝ :=
  (9554812105 / 16384 : ℝ)*u^3 + (27354794427 / 32768 : ℝ)*u^2*v^1 + (28779871899 / 16384 : ℝ)*u^2*w^1 + (6895718727 / 16384 : ℝ)*u^1*v^2 + (13749267879 / 8192 : ℝ)*u^1*v^1*w^1 + (7222814769 / 4096 : ℝ)*u^1*w^2 + (2489222293 / 32768 : ℝ)*v^3 + (6941571855 / 16384 : ℝ)*v^2*w^1 + (3454728183 / 4096 : ℝ)*v^1*w^2 + (302067953 / 512 : ℝ)*w^3

private theorem form_01032_pos : ConePositive form_01032 := by
  intro u v w hu hv hw hs
  unfold form_01032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01033 (u v w : ℝ) : ℝ :=
  (9554812105 / 16384 : ℝ)*u^3 + (27123923259 / 32768 : ℝ)*u^2*v^1 + (27354794427 / 32768 : ℝ)*u^2*w^1 + (6747928989 / 16384 : ℝ)*u^1*v^2 + (13647696123 / 16384 : ℝ)*u^1*v^1*w^1 + (6895718727 / 16384 : ℝ)*u^1*w^2 + (18696203 / 256 : ℝ)*v^3 + (3639901371 / 16384 : ℝ)*v^2*w^1 + (7375960623 / 32768 : ℝ)*v^1*w^2 + (2489222293 / 32768 : ℝ)*w^3

private theorem form_01033_pos : ConePositive form_01033 := by
  intro u v w hu hv hw hs
  unfold form_01033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0103 (u v w : ℝ) : ℝ :=
  (2358838225 / 4096 : ℝ)*u^3 + (-93132165 / 1024 : ℝ)*u^2*v^1 + (7138243695 / 4096 : ℝ)*u^2*w^1 + (366241239 / 4096 : ℝ)*u^1*v^2 + (-356187153 / 2048 : ℝ)*u^1*v^1*w^1 + (3597999333 / 2048 : ℝ)*u^1*w^2 + (10140795 / 1024 : ℝ)*v^3 + (372289995 / 4096 : ℝ)*v^2*w^1 + (-170087253 / 2048 : ℝ)*v^1*w^2 + (302067953 / 512 : ℝ)*w^3

private theorem form_0103_pos : ConePositive form_0103 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0103 (u+v/2+w/2) (v/2) (w/2)) = form_01030 := by
      funext u v w; dsimp [form_0103, form_01030]; ring
    rw [he]
    exact form_01030_pos
  · have he : (fun u v w : ℝ => form_0103 (u/2) (u/2+v+w/2) (w/2)) = form_01031 := by
      funext u v w; dsimp [form_0103, form_01031]; ring
    rw [he]
    exact form_01031_pos
  · have he : (fun u v w : ℝ => form_0103 (u/2) (v/2) (u/2+v/2+w)) = form_01032 := by
      funext u v w; dsimp [form_0103, form_01032]; ring
    rw [he]
    exact form_01032_pos
  · have he : (fun u v w : ℝ => form_0103 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_01033 := by
      funext u v w; dsimp [form_0103, form_01033]; ring
    rw [he]
    exact form_01033_pos

private def form_010 (u v w : ℝ) : ℝ :=
  (133731 / 16 : ℝ)*u^3 + (904851 / 32 : ℝ)*u^2*v^1 + (17389467 / 128 : ℝ)*u^2*w^1 + (2003373 / 64 : ℝ)*u^1*v^2 + (39038103 / 128 : ℝ)*u^1*v^1*w^1 + (-2883459 / 4 : ℝ)*u^1*w^2 + (1444797 / 128 : ℝ)*v^3 + (82710567 / 512 : ℝ)*v^2*w^1 + (-40753731 / 64 : ℝ)*v^1*w^2 + (2654083717 / 512 : ℝ)*w^3

private theorem form_010_pos : ConePositive form_010 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_010 (u+v/2+w/2) (v/2) (w/2)) = form_0100 := by
      funext u v w; dsimp [form_010, form_0100]; ring
    rw [he]
    exact form_0100_pos
  · have he : (fun u v w : ℝ => form_010 (u/2) (u/2+v+w/2) (w/2)) = form_0101 := by
      funext u v w; dsimp [form_010, form_0101]; ring
    rw [he]
    exact form_0101_pos
  · have he : (fun u v w : ℝ => form_010 (u/2) (v/2) (u/2+v/2+w)) = form_0102 := by
      funext u v w; dsimp [form_010, form_0102]; ring
    rw [he]
    exact form_0102_pos
  · have he : (fun u v w : ℝ => form_010 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0103 := by
      funext u v w; dsimp [form_010, form_0103]; ring
    rw [he]
    exact form_0103_pos

private def form_01100 (u v w : ℝ) : ℝ :=
  (1444797 / 128 : ℝ)*u^3 + (17665209 / 512 : ℝ)*u^2*v^1 + (136033839 / 2048 : ℝ)*u^2*w^1 + (71911719 / 2048 : ℝ)*u^1*v^2 + (552462669 / 4096 : ℝ)*u^1*v^1*w^1 + (85791261 / 2048 : ℝ)*u^1*w^2 + (97458147 / 8192 : ℝ)*v^3 + (2238410871 / 32768 : ℝ)*v^2*w^1 + (361491267 / 8192 : ℝ)*v^1*w^2 + (2654431729 / 32768 : ℝ)*w^3

private theorem form_01100_pos : ConePositive form_01100 := by
  intro u v w hu hv hw hs
  unfold form_01100
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01101 (u v w : ℝ) : ℝ :=
  (97458147 / 8192 : ℝ)*u^3 + (148551003 / 4096 : ℝ)*u^2*v^1 + (2257321131 / 32768 : ℝ)*u^2*w^1 + (75388401 / 2048 : ℝ)*u^1*v^2 + (1142388729 / 8192 : ℝ)*u^1*v^1*w^1 + (750990795 / 16384 : ℝ)*u^1*w^2 + (12737169 / 1024 : ℝ)*v^3 + (576834003 / 8192 : ℝ)*v^2*w^1 + (391409913 / 8192 : ℝ)*v^1*w^2 + (340367249 / 4096 : ℝ)*w^3

private theorem form_01101_pos : ConePositive form_01101 := by
  intro u v w hu hv hw hs
  unfold form_01101
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01102 (u v w : ℝ) : ℝ :=
  (2654431729 / 32768 : ℝ)*u^3 + (8036600079 / 32768 : ℝ)*u^2*v^1 + (7276965099 / 16384 : ℝ)*u^2*w^1 + (4052577957 / 16384 : ℝ)*u^1*v^2 + (7333615365 / 8192 : ℝ)*u^1*v^1*w^1 + (7134770367 / 8192 : ℝ)*u^1*w^2 + (340367249 / 4096 : ℝ)*v^3 + (3692997075 / 8192 : ℝ)*v^2*w^1 + (7180008327 / 8192 : ℝ)*v^1*w^2 + (2466003493 / 4096 : ℝ)*w^3

private theorem form_01102_pos : ConePositive form_01102 := by
  intro u v w hu hv hw hs
  unfold form_01102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01103 (u v w : ℝ) : ℝ :=
  (2654431729 / 32768 : ℝ)*u^3 + (361491267 / 8192 : ℝ)*u^2*v^1 + (8036600079 / 32768 : ℝ)*u^2*w^1 + (2238410871 / 32768 : ℝ)*u^1*v^2 + (1474525263 / 16384 : ℝ)*u^1*v^1*w^1 + (4052577957 / 16384 : ℝ)*u^1*w^2 + (97458147 / 8192 : ℝ)*v^3 + (2257321131 / 32768 : ℝ)*v^2*w^1 + (750990795 / 16384 : ℝ)*v^1*w^2 + (340367249 / 4096 : ℝ)*w^3

private theorem form_01103_pos : ConePositive form_01103 := by
  intro u v w hu hv hw hs
  unfold form_01103
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0110 (u v w : ℝ) : ℝ :=
  (1444797 / 128 : ℝ)*u^3 + (8996427 / 256 : ℝ)*u^2*v^1 + (101358711 / 1024 : ℝ)*u^2*w^1 + (18588447 / 512 : ℝ)*u^1*v^2 + (208423575 / 1024 : ℝ)*u^1*v^1*w^1 + (-16452507 / 256 : ℝ)*u^1*w^2 + (12737169 / 1024 : ℝ)*v^3 + (423987975 / 4096 : ℝ)*v^2*w^1 + (-27250269 / 512 : ℝ)*v^1*w^2 + (2466003493 / 4096 : ℝ)*w^3

private theorem form_0110_pos : ConePositive form_0110 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0110 (u+v/2+w/2) (v/2) (w/2)) = form_01100 := by
      funext u v w; dsimp [form_0110, form_01100]; ring
    rw [he]
    exact form_01100_pos
  · have he : (fun u v w : ℝ => form_0110 (u/2) (u/2+v+w/2) (w/2)) = form_01101 := by
      funext u v w; dsimp [form_0110, form_01101]; ring
    rw [he]
    exact form_01101_pos
  · have he : (fun u v w : ℝ => form_0110 (u/2) (v/2) (u/2+v/2+w)) = form_01102 := by
      funext u v w; dsimp [form_0110, form_01102]; ring
    rw [he]
    exact form_01102_pos
  · have he : (fun u v w : ℝ => form_0110 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_01103 := by
      funext u v w; dsimp [form_0110, form_01103]; ring
    rw [he]
    exact form_01103_pos

private def form_01110 (u v w : ℝ) : ℝ :=
  (12737169 / 1024 : ℝ)*u^3 + (77457627 / 2048 : ℝ)*u^2*v^1 + (580972455 / 8192 : ℝ)*u^2*w^1 + (156827907 / 4096 : ℝ)*u^1*v^2 + (1172597895 / 8192 : ℝ)*u^1*v^1*w^1 + (100594011 / 2048 : ℝ)*u^1*w^2 + (105710265 / 8192 : ℝ)*v^3 + (2361455271 / 32768 : ℝ)*v^2*w^1 + (207902247 / 4096 : ℝ)*v^1*w^2 + (2781648709 / 32768 : ℝ)*w^3

private theorem form_01110_pos : ConePositive form_01110 := by
  intro u v w hu hv hw hs
  unfold form_01110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01111 (u v w : ℝ) : ℝ :=
  (105710265 / 8192 : ℝ)*u^3 + (20037861 / 512 : ℝ)*u^2*v^1 + (2375355195 / 32768 : ℝ)*u^2*w^1 + (316143 / 8 : ℝ)*u^1*v^2 + (9336771 / 64 : ℝ)*u^1*v^1*w^1 + (847167819 / 16384 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (9374517 / 128 : ℝ)*v^2*w^1 + (13576623 / 256 : ℝ)*v^1*w^2 + (176891653 / 2048 : ℝ)*w^3

private theorem form_01111_pos : ConePositive form_01111 := by
  intro u v w hu hv hw hs
  unfold form_01111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01112 (u v w : ℝ) : ℝ :=
  (2781648709 / 32768 : ℝ)*u^3 + (8398659927 / 32768 : ℝ)*u^2*v^1 + (7540194039 / 16384 : ℝ)*u^2*w^1 + (4223663619 / 16384 : ℝ)*u^1*v^2 + (3791627427 / 4096 : ℝ)*u^1*v^1*w^1 + (3658207203 / 4096 : ℝ)*u^1*w^2 + (176891653 / 2048 : ℝ)*v^3 + (476368467 / 1024 : ℝ)*v^2*w^1 + (459560043 / 512 : ℝ)*v^1*w^2 + (156682525 / 256 : ℝ)*w^3

private theorem form_01112_pos : ConePositive form_01112 := by
  intro u v w hu hv hw hs
  unfold form_01112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01113 (u v w : ℝ) : ℝ :=
  (2781648709 / 32768 : ℝ)*u^3 + (207902247 / 4096 : ℝ)*u^2*v^1 + (8398659927 / 32768 : ℝ)*u^2*w^1 + (2361455271 / 32768 : ℝ)*u^1*v^2 + (1679477457 / 16384 : ℝ)*u^1*v^1*w^1 + (4223663619 / 16384 : ℝ)*u^1*w^2 + (105710265 / 8192 : ℝ)*v^3 + (2375355195 / 32768 : ℝ)*v^2*w^1 + (847167819 / 16384 : ℝ)*v^1*w^2 + (176891653 / 2048 : ℝ)*w^3

private theorem form_01113_pos : ConePositive form_01113 := by
  intro u v w hu hv hw hs
  unfold form_01113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0111 (u v w : ℝ) : ℝ :=
  (12737169 / 1024 : ℝ)*u^3 + (4905765 / 128 : ℝ)*u^2*v^1 + (428126427 / 4096 : ℝ)*u^2*w^1 + (156735 / 4 : ℝ)*u^1*v^2 + (6791265 / 32 : ℝ)*u^1*v^1*w^1 + (-102173397 / 2048 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (6823989 / 64 : ℝ)*v^2*w^1 + (-2621883 / 64 : ℝ)*v^1*w^2 + (156682525 / 256 : ℝ)*w^3

private theorem form_0111_pos : ConePositive form_0111 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0111 (u+v/2+w/2) (v/2) (w/2)) = form_01110 := by
      funext u v w; dsimp [form_0111, form_01110]; ring
    rw [he]
    exact form_01110_pos
  · have he : (fun u v w : ℝ => form_0111 (u/2) (u/2+v+w/2) (w/2)) = form_01111 := by
      funext u v w; dsimp [form_0111, form_01111]; ring
    rw [he]
    exact form_01111_pos
  · have he : (fun u v w : ℝ => form_0111 (u/2) (v/2) (u/2+v/2+w)) = form_01112 := by
      funext u v w; dsimp [form_0111, form_01112]; ring
    rw [he]
    exact form_01112_pos
  · have he : (fun u v w : ℝ => form_0111 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_01113 := by
      funext u v w; dsimp [form_0111, form_01113]; ring
    rw [he]
    exact form_01113_pos

private def form_0112 (u v w : ℝ) : ℝ :=
  (2466003493 / 4096 : ℝ)*u^3 + (7443248439 / 4096 : ℝ)*u^2*v^1 + (7529630535 / 2048 : ℝ)*u^2*w^1 + (3742107459 / 2048 : ℝ)*u^1*v^2 + (3784581171 / 512 : ℝ)*u^1*v^1*w^1 + (3881304651 / 512 : ℝ)*u^1*w^2 + (156682525 / 256 : ℝ)*v^3 + (475291341 / 128 : ℝ)*v^2*w^1 + (60919887 / 8 : ℝ)*v^1*w^2 + (21040649 / 4 : ℝ)*w^3

private theorem form_0112_pos : ConePositive form_0112 := by
  intro u v w hu hv hw hs
  unfold form_0112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01130 (u v w : ℝ) : ℝ :=
  (2466003493 / 4096 : ℝ)*u^3 + (7180008327 / 8192 : ℝ)*u^2*v^1 + (7420629459 / 4096 : ℝ)*u^2*w^1 + (3692997075 / 8192 : ℝ)*u^1*v^2 + (14412395439 / 8192 : ℝ)*u^1*v^1*w^1 + (29768722275 / 16384 : ℝ)*u^1*w^2 + (340367249 / 4096 : ℝ)*v^3 + (7417823181 / 16384 : ℝ)*v^2*w^1 + (28924650675 / 32768 : ℝ)*v^1*w^2 + (9950193625 / 16384 : ℝ)*w^3

private theorem form_01130_pos : ConePositive form_01130 := by
  intro u v w hu hv hw hs
  unfold form_01130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01131 (u v w : ℝ) : ℝ :=
  (340367249 / 4096 : ℝ)*u^3 + (391409913 / 8192 : ℝ)*u^2*v^1 + (4116236019 / 16384 : ℝ)*u^2*w^1 + (576834003 / 8192 : ℝ)*u^1*v^2 + (794099103 / 8192 : ℝ)*u^1*v^1*w^1 + (8291232327 / 32768 : ℝ)*u^1*w^2 + (12737169 / 1024 : ℝ)*v^3 + (580972455 / 8192 : ℝ)*v^2*w^1 + (100594011 / 2048 : ℝ)*v^1*w^2 + (2781648709 / 32768 : ℝ)*w^3

private theorem form_01131_pos : ConePositive form_01131 := by
  intro u v w hu hv hw hs
  unfold form_01131
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01132 (u v w : ℝ) : ℝ :=
  (9950193625 / 16384 : ℝ)*u^3 + (29088367875 / 32768 : ℝ)*u^2*v^1 + (29932439475 / 16384 : ℝ)*u^2*w^1 + (7513337139 / 16384 : ℝ)*u^1*v^2 + (14589767997 / 8192 : ℝ)*u^1*v^1*w^1 + (7502488059 / 4096 : ℝ)*u^1*w^2 + (2781648709 / 32768 : ℝ)*v^3 + (7540194039 / 16384 : ℝ)*v^2*w^1 + (3658207203 / 4096 : ℝ)*v^1*w^2 + (156682525 / 256 : ℝ)*w^3

private theorem form_01132_pos : ConePositive form_01132 := by
  intro u v w hu hv hw hs
  unfold form_01132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01133 (u v w : ℝ) : ℝ :=
  (9950193625 / 16384 : ℝ)*u^3 + (28924650675 / 32768 : ℝ)*u^2*v^1 + (29088367875 / 32768 : ℝ)*u^2*w^1 + (7417823181 / 16384 : ℝ)*u^1*v^2 + (14935506159 / 16384 : ℝ)*u^1*v^1*w^1 + (7513337139 / 16384 : ℝ)*u^1*w^2 + (340367249 / 4096 : ℝ)*v^3 + (4116236019 / 16384 : ℝ)*v^2*w^1 + (8291232327 / 32768 : ℝ)*v^1*w^2 + (2781648709 / 32768 : ℝ)*w^3

private theorem form_01133_pos : ConePositive form_01133 := by
  intro u v w hu hv hw hs
  unfold form_01133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0113 (u v w : ℝ) : ℝ :=
  (2466003493 / 4096 : ℝ)*u^3 + (-27250269 / 512 : ℝ)*u^2*v^1 + (7443248439 / 4096 : ℝ)*u^2*w^1 + (423987975 / 4096 : ℝ)*u^1*v^2 + (-210861327 / 2048 : ℝ)*u^1*v^1*w^1 + (3742107459 / 2048 : ℝ)*u^1*w^2 + (12737169 / 1024 : ℝ)*v^3 + (428126427 / 4096 : ℝ)*v^2*w^1 + (-102173397 / 2048 : ℝ)*v^1*w^2 + (156682525 / 256 : ℝ)*w^3

private theorem form_0113_pos : ConePositive form_0113 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0113 (u+v/2+w/2) (v/2) (w/2)) = form_01130 := by
      funext u v w; dsimp [form_0113, form_01130]; ring
    rw [he]
    exact form_01130_pos
  · have he : (fun u v w : ℝ => form_0113 (u/2) (u/2+v+w/2) (w/2)) = form_01131 := by
      funext u v w; dsimp [form_0113, form_01131]; ring
    rw [he]
    exact form_01131_pos
  · have he : (fun u v w : ℝ => form_0113 (u/2) (v/2) (u/2+v/2+w)) = form_01132 := by
      funext u v w; dsimp [form_0113, form_01132]; ring
    rw [he]
    exact form_01132_pos
  · have he : (fun u v w : ℝ => form_0113 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_01133 := by
      funext u v w; dsimp [form_0113, form_01133]; ring
    rw [he]
    exact form_01133_pos

private def form_011 (u v w : ℝ) : ℝ :=
  (1444797 / 128 : ℝ)*u^3 + (1165509 / 32 : ℝ)*u^2*v^1 + (84021147 / 512 : ℝ)*u^2*w^1 + (77031 / 2 : ℝ)*u^1*v^2 + (5526045 / 16 : ℝ)*u^1*v^1*w^1 + (-158499957 / 256 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (5548725 / 32 : ℝ)*v^2*w^1 + (-550515 / 1 : ℝ)*v^1*w^2 + (21040649 / 4 : ℝ)*w^3

private theorem form_011_pos : ConePositive form_011 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_011 (u+v/2+w/2) (v/2) (w/2)) = form_0110 := by
      funext u v w; dsimp [form_011, form_0110]; ring
    rw [he]
    exact form_0110_pos
  · have he : (fun u v w : ℝ => form_011 (u/2) (u/2+v+w/2) (w/2)) = form_0111 := by
      funext u v w; dsimp [form_011, form_0111]; ring
    rw [he]
    exact form_0111_pos
  · have he : (fun u v w : ℝ => form_011 (u/2) (v/2) (u/2+v/2+w)) = form_0112 := by
      funext u v w; dsimp [form_011, form_0112]; ring
    rw [he]
    exact form_0112_pos
  · have he : (fun u v w : ℝ => form_011 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0113 := by
      funext u v w; dsimp [form_011, form_0113]; ring
    rw [he]
    exact form_0113_pos

private def form_012 (u v w : ℝ) : ℝ :=
  (2654083717 / 512 : ℝ)*u^3 + (8005304055 / 512 : ℝ)*u^2*v^1 + (8146792527 / 256 : ℝ)*u^2*w^1 + (4022236491 / 256 : ℝ)*u^1*v^2 + (4092793131 / 64 : ℝ)*u^1*v^1*w^1 + (4174361685 / 64 : ℝ)*u^1*w^2 + (21040649 / 4 : ℝ)*v^3 + (64222977 / 2 : ℝ)*v^2*w^1 + (2095916949 / 32 : ℝ)*v^1*w^2 + (713869909 / 16 : ℝ)*w^3

private theorem form_012_pos : ConePositive form_012 := by
  intro u v w hu hv hw hs
  unfold form_012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0130 (u v w : ℝ) : ℝ :=
  (2654083717 / 512 : ℝ)*u^3 + (7636221303 / 1024 : ℝ)*u^2*v^1 + (7983777603 / 512 : ℝ)*u^2*w^1 + (3696451011 / 1024 : ℝ)*u^1*v^2 + (15320129871 / 1024 : ℝ)*u^1*v^1*w^1 + (32017332243 / 2048 : ℝ)*u^1*w^2 + (302067953 / 512 : ℝ)*v^3 + (7419718125 / 2048 : ℝ)*v^2*w^1 + (30731511507 / 4096 : ℝ)*v^1*w^2 + (10698531913 / 2048 : ℝ)*w^3

private theorem form_0130_pos : ConePositive form_0130 := by
  intro u v w hu hv hw hs
  unfold form_0130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01310 (u v w : ℝ) : ℝ :=
  (302067953 / 512 : ℝ)*u^3 + (1740772143 / 2048 : ℝ)*u^2*v^1 + (7276446975 / 4096 : ℝ)*u^2*w^1 + (1769184699 / 4096 : ℝ)*u^1*v^2 + (437240601 / 256 : ℝ)*u^1*v^1*w^1 + (29208929547 / 16384 : ℝ)*u^1*w^2 + (322053419 / 4096 : ℝ)*v^3 + (7118065941 / 16384 : ℝ)*v^2*w^1 + (28109842299 / 32768 : ℝ)*v^1*w^2 + (9769291357 / 16384 : ℝ)*w^3

private theorem form_01310_pos : ConePositive form_01310 := by
  intro u v w hu hv hw hs
  unfold form_01310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01311 (u v w : ℝ) : ℝ :=
  (322053419 / 4096 : ℝ)*u^3 + (163135815 / 4096 : ℝ)*u^2*v^1 + (3905968173 / 16384 : ℝ)*u^2*w^1 + (134723259 / 2048 : ℝ)*u^1*v^2 + (334837731 / 4096 : ℝ)*u^1*v^1*w^1 + (7889990295 / 32768 : ℝ)*u^1*w^2 + (1444797 / 128 : ℝ)*v^3 + (136033839 / 2048 : ℝ)*v^2*w^1 + (85791261 / 2048 : ℝ)*v^1*w^2 + (2654431729 / 32768 : ℝ)*w^3

private theorem form_01311_pos : ConePositive form_01311 := by
  intro u v w hu hv hw hs
  unfold form_01311
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01312 (u v w : ℝ) : ℝ :=
  (9769291357 / 16384 : ℝ)*u^3 + (28307731347 / 32768 : ℝ)*u^2*v^1 + (29406818595 / 16384 : ℝ)*u^2*w^1 + (7240312653 / 16384 : ℝ)*u^1*v^2 + (3553222617 / 2048 : ℝ)*u^1*v^1*w^1 + (7375391499 / 4096 : ℝ)*u^1*w^2 + (2654431729 / 32768 : ℝ)*v^3 + (7276965099 / 16384 : ℝ)*v^2*w^1 + (7134770367 / 8192 : ℝ)*v^1*w^2 + (2466003493 / 4096 : ℝ)*w^3

private theorem form_01312_pos : ConePositive form_01312 := by
  intro u v w hu hv hw hs
  unfold form_01312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_01313 (u v w : ℝ) : ℝ :=
  (9769291357 / 16384 : ℝ)*u^3 + (28109842299 / 32768 : ℝ)*u^2*v^1 + (28307731347 / 32768 : ℝ)*u^2*w^1 + (7118065941 / 16384 : ℝ)*u^1*v^2 + (14362575717 / 16384 : ℝ)*u^1*v^1*w^1 + (7240312653 / 16384 : ℝ)*u^1*w^2 + (322053419 / 4096 : ℝ)*v^3 + (3905968173 / 16384 : ℝ)*v^2*w^1 + (7889990295 / 32768 : ℝ)*v^1*w^2 + (2654431729 / 32768 : ℝ)*w^3

private theorem form_01313_pos : ConePositive form_01313 := by
  intro u v w hu hv hw hs
  unfold form_01313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0131 (u v w : ℝ) : ℝ :=
  (302067953 / 512 : ℝ)*u^3 + (-71635575 / 1024 : ℝ)*u^2*v^1 + (3651631539 / 2048 : ℝ)*u^2*w^1 + (100048131 / 1024 : ℝ)*u^1*v^2 + (-137326209 / 1024 : ℝ)*u^1*v^1*w^1 + (7352772519 / 4096 : ℝ)*u^1*w^2 + (1444797 / 128 : ℝ)*v^3 + (101358711 / 1024 : ℝ)*v^2*w^1 + (-16452507 / 256 : ℝ)*v^1*w^2 + (2466003493 / 4096 : ℝ)*w^3

private theorem form_0131_pos : ConePositive form_0131 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0131 (u+v/2+w/2) (v/2) (w/2)) = form_01310 := by
      funext u v w; dsimp [form_0131, form_01310]; ring
    rw [he]
    exact form_01310_pos
  · have he : (fun u v w : ℝ => form_0131 (u/2) (u/2+v+w/2) (w/2)) = form_01311 := by
      funext u v w; dsimp [form_0131, form_01311]; ring
    rw [he]
    exact form_01311_pos
  · have he : (fun u v w : ℝ => form_0131 (u/2) (v/2) (u/2+v/2+w)) = form_01312 := by
      funext u v w; dsimp [form_0131, form_01312]; ring
    rw [he]
    exact form_01312_pos
  · have he : (fun u v w : ℝ => form_0131 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_01313 := by
      funext u v w; dsimp [form_0131, form_01313]; ring
    rw [he]
    exact form_01313_pos

private def form_0132 (u v w : ℝ) : ℝ :=
  (10698531913 / 2048 : ℝ)*u^3 + (30888038499 / 4096 : ℝ)*u^2*v^1 + (32173859235 / 2048 : ℝ)*u^2*w^1 + (7507011555 / 2048 : ℝ)*u^1*v^2 + (15485686797 / 1024 : ℝ)*u^1*v^1*w^1 + (8062041099 / 512 : ℝ)*u^1*w^2 + (2466003493 / 4096 : ℝ)*v^3 + (7529630535 / 2048 : ℝ)*v^2*w^1 + (3881304651 / 512 : ℝ)*v^1*w^2 + (21040649 / 4 : ℝ)*w^3

private theorem form_0132_pos : ConePositive form_0132 := by
  intro u v w hu hv hw hs
  unfold form_0132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0133 (u v w : ℝ) : ℝ :=
  (10698531913 / 2048 : ℝ)*u^3 + (30731511507 / 4096 : ℝ)*u^2*v^1 + (30888038499 / 4096 : ℝ)*u^2*w^1 + (7419718125 / 2048 : ℝ)*u^1*v^2 + (14930688015 / 2048 : ℝ)*u^1*v^1*w^1 + (7507011555 / 2048 : ℝ)*u^1*w^2 + (302067953 / 512 : ℝ)*v^3 + (3651631539 / 2048 : ℝ)*v^2*w^1 + (7352772519 / 4096 : ℝ)*v^1*w^2 + (2466003493 / 4096 : ℝ)*w^3

private theorem form_0133_pos : ConePositive form_0133 := by
  intro u v w hu hv hw hs
  unfold form_0133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_013 (u v w : ℝ) : ℝ :=
  (2654083717 / 512 : ℝ)*u^3 + (-40753731 / 64 : ℝ)*u^2*v^1 + (8005304055 / 512 : ℝ)*u^2*w^1 + (82710567 / 512 : ℝ)*u^1*v^2 + (-321395487 / 256 : ℝ)*u^1*v^1*w^1 + (4022236491 / 256 : ℝ)*u^1*w^2 + (1444797 / 128 : ℝ)*v^3 + (84021147 / 512 : ℝ)*v^2*w^1 + (-158499957 / 256 : ℝ)*v^1*w^2 + (21040649 / 4 : ℝ)*w^3

private theorem form_013_pos : ConePositive form_013 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_013 (u+v/2+w/2) (v/2) (w/2)) = form_0130 := by
      funext u v w; dsimp [form_013, form_0130]; ring
    rw [he]
    exact form_0130_pos
  · have he : (fun u v w : ℝ => form_013 (u/2) (u/2+v+w/2) (w/2)) = form_0131 := by
      funext u v w; dsimp [form_013, form_0131]; ring
    rw [he]
    exact form_0131_pos
  · have he : (fun u v w : ℝ => form_013 (u/2) (v/2) (u/2+v/2+w)) = form_0132 := by
      funext u v w; dsimp [form_013, form_0132]; ring
    rw [he]
    exact form_0132_pos
  · have he : (fun u v w : ℝ => form_013 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0133 := by
      funext u v w; dsimp [form_013, form_0133]; ring
    rw [he]
    exact form_0133_pos

private def form_01 (u v w : ℝ) : ℝ :=
  (133731 / 16 : ℝ)*u^3 + (251829 / 8 : ℝ)*u^2*v^1 + (15784695 / 64 : ℝ)*u^2*w^1 + (37179 / 1 : ℝ)*u^1*v^2 + (4908501 / 8 : ℝ)*u^1*v^1*w^1 + (-108857769 / 32 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (4911093 / 16 : ℝ)*v^2*w^1 + (-22846389 / 8 : ℝ)*v^1*w^2 + (713869909 / 16 : ℝ)*w^3

private theorem form_01_pos : ConePositive form_01 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_01 (u+v/2+w/2) (v/2) (w/2)) = form_010 := by
      funext u v w; dsimp [form_01, form_010]; ring
    rw [he]
    exact form_010_pos
  · have he : (fun u v w : ℝ => form_01 (u/2) (u/2+v+w/2) (w/2)) = form_011 := by
      funext u v w; dsimp [form_01, form_011]; ring
    rw [he]
    exact form_011_pos
  · have he : (fun u v w : ℝ => form_01 (u/2) (v/2) (u/2+v/2+w)) = form_012 := by
      funext u v w; dsimp [form_01, form_012]; ring
    rw [he]
    exact form_012_pos
  · have he : (fun u v w : ℝ => form_01 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_013 := by
      funext u v w; dsimp [form_01, form_013]; ring
    rw [he]
    exact form_013_pos

private def form_02 (u v w : ℝ) : ℝ :=
  (2816745841 / 64 : ℝ)*u^3 + (8492711115 / 64 : ℝ)*u^2*v^1 + (8584203915 / 32 : ℝ)*u^2*w^1 + (4265747241 / 32 : ℝ)*u^1*v^2 + (4311442611 / 8 : ℝ)*u^1*v^1*w^1 + (8719144287 / 16 : ℝ)*u^1*w^2 + (713869909 / 16 : ℝ)*v^3 + (541114029 / 2 : ℝ)*v^2*w^1 + (8754121113 / 16 : ℝ)*v^1*w^2 + (2951670013 / 8 : ℝ)*w^3

private theorem form_02_pos : ConePositive form_02 := by
  intro u v w hu hv hw hs
  unfold form_02
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_030 (u v w : ℝ) : ℝ :=
  (2816745841 / 64 : ℝ)*u^3 + (8224778331 / 128 : ℝ)*u^2*v^1 + (8471474319 / 64 : ℝ)*u^2*w^1 + (4007346987 / 128 : ℝ)*u^1*v^2 + (16495924599 / 128 : ℝ)*u^1*v^1*w^1 + (33967154235 / 256 : ℝ)*u^1*w^2 + (325899551 / 64 : ℝ)*v^3 + (8040030045 / 256 : ℝ)*v^2*w^1 + (33080849811 / 512 : ℝ)*v^1*w^2 + (11348215537 / 256 : ℝ)*w^3

private theorem form_030_pos : ConePositive form_030 := by
  intro u v w hu hv hw hs
  unfold form_030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0310 (u v w : ℝ) : ℝ :=
  (325899551 / 64 : ℝ)*u^3 + (1858844931 / 256 : ℝ)*u^2*v^1 + (7846925295 / 512 : ℝ)*u^2*w^1 + (1779272163 / 512 : ℝ)*u^1*v^2 + (233281875 / 16 : ℝ)*u^1*v^1*w^1 + (31485310203 / 2048 : ℝ)*u^1*w^2 + (286648091 / 512 : ℝ)*v^3 + (7151852853 / 2048 : ℝ)*v^2*w^1 + (29974815771 / 4096 : ℝ)*v^1*w^2 + (10526369869 / 2048 : ℝ)*w^3

private theorem form_0310_pos : ConePositive form_0310 := by
  intro u v w hu hv hw hs
  unfold form_0310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_03110 (u v w : ℝ) : ℝ :=
  (286648091 / 512 : ℝ)*u^3 + (50035041 / 64 : ℝ)*u^2*v^1 + (6914318385 / 4096 : ℝ)*u^2*w^1 + (781555341 / 2048 : ℝ)*u^1*v^2 + (6449497299 / 4096 : ℝ)*u^1*v^1*w^1 + (27792505011 / 16384 : ℝ)*u^1*w^2 + (33990271 / 512 : ℝ)*v^3 + (6310981509 / 16384 : ℝ)*v^2*w^1 + (25974031923 / 32768 : ℝ)*v^1*w^2 + (9307945597 / 16384 : ℝ)*w^3

private theorem form_03110_pos : ConePositive form_03110 := by
  intro u v w hu hv hw hs
  unfold form_03110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_03111 (u v w : ℝ) : ℝ :=
  (33990271 / 512 : ℝ)*u^3 + (34211163 / 2048 : ℝ)*u^2*v^1 + (3321604797 / 16384 : ℝ)*u^2*w^1 + (26608239 / 512 : ℝ)*u^1*v^2 + (75185691 / 2048 : ℝ)*u^1*v^1*w^1 + (6756281679 / 32768 : ℝ)*u^1*w^2 + (133731 / 16 : ℝ)*v^3 + (27018099 / 512 : ℝ)*v^2*w^1 + (20476005 / 1024 : ℝ)*v^1*w^2 + (2288399857 / 32768 : ℝ)*w^3

private theorem form_03111_pos : ConePositive form_03111 := by
  intro u v w hu hv hw hs
  unfold form_03111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_03112 (u v w : ℝ) : ℝ :=
  (9307945597 / 16384 : ℝ)*u^3 + (26236695483 / 32768 : ℝ)*u^2*v^1 + (28055168571 / 16384 : ℝ)*u^2*w^1 + (6483124545 / 16384 : ℝ)*u^1*v^2 + (6601234707 / 4096 : ℝ)*u^1*v^1*w^1 + (7045650165 / 4096 : ℝ)*u^1*w^2 + (2288399857 / 32768 : ℝ)*v^3 + (6537583491 / 16384 : ℝ)*v^2*w^1 + (6642256995 / 8192 : ℝ)*v^1*w^2 + (2358838225 / 4096 : ℝ)*w^3

private theorem form_03112_pos : ConePositive form_03112 := by
  intro u v w hu hv hw hs
  unfold form_03112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_03113 (u v w : ℝ) : ℝ :=
  (9307945597 / 16384 : ℝ)*u^3 + (25974031923 / 32768 : ℝ)*u^2*v^1 + (26236695483 / 32768 : ℝ)*u^2*w^1 + (6310981509 / 16384 : ℝ)*u^1*v^2 + (12798005745 / 16384 : ℝ)*u^1*v^1*w^1 + (6483124545 / 16384 : ℝ)*u^1*w^2 + (33990271 / 512 : ℝ)*v^3 + (3321604797 / 16384 : ℝ)*v^2*w^1 + (6756281679 / 32768 : ℝ)*v^1*w^2 + (2288399857 / 32768 : ℝ)*w^3

private theorem form_03113_pos : ConePositive form_03113 := by
  intro u v w hu hv hw hs
  unfold form_03113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0311 (u v w : ℝ) : ℝ :=
  (286648091 / 512 : ℝ)*u^3 + (-59383617 / 512 : ℝ)*u^2*v^1 + (3474541293 / 2048 : ℝ)*u^2*w^1 + (20189151 / 256 : ℝ)*u^1*v^2 + (-113643309 / 512 : ℝ)*u^1*v^1*w^1 + (7014785655 / 4096 : ℝ)*u^1*w^2 + (133731 / 16 : ℝ)*v^3 + (20599011 / 256 : ℝ)*v^2*w^1 + (-27141105 / 256 : ℝ)*v^1*w^2 + (2358838225 / 4096 : ℝ)*w^3

private theorem form_0311_pos : ConePositive form_0311 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0311 (u+v/2+w/2) (v/2) (w/2)) = form_03110 := by
      funext u v w; dsimp [form_0311, form_03110]; ring
    rw [he]
    exact form_03110_pos
  · have he : (fun u v w : ℝ => form_0311 (u/2) (u/2+v+w/2) (w/2)) = form_03111 := by
      funext u v w; dsimp [form_0311, form_03111]; ring
    rw [he]
    exact form_03111_pos
  · have he : (fun u v w : ℝ => form_0311 (u/2) (v/2) (u/2+v/2+w)) = form_03112 := by
      funext u v w; dsimp [form_0311, form_03112]; ring
    rw [he]
    exact form_03112_pos
  · have he : (fun u v w : ℝ => form_0311 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_03113 := by
      funext u v w; dsimp [form_0311, form_03113]; ring
    rw [he]
    exact form_03113_pos

private def form_0312 (u v w : ℝ) : ℝ :=
  (10526369869 / 2048 : ℝ)*u^3 + (30162414579 / 4096 : ℝ)*u^2*v^1 + (31672909011 / 2048 : ℝ)*u^2*w^1 + (7262779005 / 2048 : ℝ)*u^1*v^2 + (3783691389 / 256 : ℝ)*u^1*v^1*w^1 + (7940724699 / 512 : ℝ)*u^1*w^2 + (2358838225 / 4096 : ℝ)*v^3 + (7293643515 / 2048 : ℝ)*v^2*w^1 + (7593168399 / 1024 : ℝ)*v^1*w^2 + (2654083717 / 512 : ℝ)*w^3

private theorem form_0312_pos : ConePositive form_0312 := by
  intro u v w hu hv hw hs
  unfold form_0312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_0313 (u v w : ℝ) : ℝ :=
  (10526369869 / 2048 : ℝ)*u^3 + (29974815771 / 4096 : ℝ)*u^2*v^1 + (30162414579 / 4096 : ℝ)*u^2*w^1 + (7151852853 / 2048 : ℝ)*u^1*v^2 + (14418441477 / 2048 : ℝ)*u^1*v^1*w^1 + (7262779005 / 2048 : ℝ)*u^1*w^2 + (286648091 / 512 : ℝ)*v^3 + (3474541293 / 2048 : ℝ)*v^2*w^1 + (7014785655 / 4096 : ℝ)*v^1*w^2 + (2358838225 / 4096 : ℝ)*w^3

private theorem form_0313_pos : ConePositive form_0313 := by
  intro u v w hu hv hw hs
  unfold form_0313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_031 (u v w : ℝ) : ℝ :=
  (325899551 / 64 : ℝ)*u^3 + (-96552375 / 128 : ℝ)*u^2*v^1 + (3936130683 / 256 : ℝ)*u^2*w^1 + (16979607 / 128 : ℝ)*u^1*v^2 + (-188800545 / 128 : ℝ)*u^1*v^1*w^1 + (7919198247 / 512 : ℝ)*u^1*w^2 + (133731 / 16 : ℝ)*v^3 + (17389467 / 128 : ℝ)*v^2*w^1 + (-2883459 / 4 : ℝ)*v^1*w^2 + (2654083717 / 512 : ℝ)*w^3

private theorem form_031_pos : ConePositive form_031 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_031 (u+v/2+w/2) (v/2) (w/2)) = form_0310 := by
      funext u v w; dsimp [form_031, form_0310]; ring
    rw [he]
    exact form_0310_pos
  · have he : (fun u v w : ℝ => form_031 (u/2) (u/2+v+w/2) (w/2)) = form_0311 := by
      funext u v w; dsimp [form_031, form_0311]; ring
    rw [he]
    exact form_0311_pos
  · have he : (fun u v w : ℝ => form_031 (u/2) (v/2) (u/2+v/2+w)) = form_0312 := by
      funext u v w; dsimp [form_031, form_0312]; ring
    rw [he]
    exact form_0312_pos
  · have he : (fun u v w : ℝ => form_031 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_0313 := by
      funext u v w; dsimp [form_031, form_0313]; ring
    rw [he]
    exact form_0313_pos

private def form_032 (u v w : ℝ) : ℝ :=
  (11348215537 / 256 : ℝ)*u^3 + (33235834563 / 512 : ℝ)*u^2*v^1 + (34122138987 / 256 : ℝ)*u^2*w^1 + (8125266075 / 256 : ℝ)*u^1*v^2 + (16658653005 / 128 : ℝ)*u^1*v^1*w^1 + (8548966695 / 64 : ℝ)*u^1*w^2 + (2654083717 / 512 : ℝ)*v^3 + (8146792527 / 256 : ℝ)*v^2*w^1 + (4174361685 / 64 : ℝ)*v^1*w^2 + (713869909 / 16 : ℝ)*w^3

private theorem form_032_pos : ConePositive form_032 := by
  intro u v w hu hv hw hs
  unfold form_032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_033 (u v w : ℝ) : ℝ :=
  (11348215537 / 256 : ℝ)*u^3 + (33080849811 / 512 : ℝ)*u^2*v^1 + (33235834563 / 512 : ℝ)*u^2*w^1 + (8040030045 / 256 : ℝ)*u^1*v^2 + (16169060703 / 256 : ℝ)*u^1*v^1*w^1 + (8125266075 / 256 : ℝ)*u^1*w^2 + (325899551 / 64 : ℝ)*v^3 + (3936130683 / 256 : ℝ)*v^2*w^1 + (7919198247 / 512 : ℝ)*v^1*w^2 + (2654083717 / 512 : ℝ)*w^3

private theorem form_033_pos : ConePositive form_033 := by
  intro u v w hu hv hw hs
  unfold form_033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_03 (u v w : ℝ) : ℝ :=
  (2816745841 / 64 : ℝ)*u^3 + (-28182399 / 8 : ℝ)*u^2*v^1 + (8492711115 / 64 : ℝ)*u^2*w^1 + (15374835 / 64 : ℝ)*u^1*v^2 + (-221564847 / 32 : ℝ)*u^1*v^1*w^1 + (4265747241 / 32 : ℝ)*u^1*w^2 + (133731 / 16 : ℝ)*v^3 + (15784695 / 64 : ℝ)*v^2*w^1 + (-108857769 / 32 : ℝ)*v^1*w^2 + (713869909 / 16 : ℝ)*w^3

private theorem form_03_pos : ConePositive form_03 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_03 (u+v/2+w/2) (v/2) (w/2)) = form_030 := by
      funext u v w; dsimp [form_03, form_030]; ring
    rw [he]
    exact form_030_pos
  · have he : (fun u v w : ℝ => form_03 (u/2) (u/2+v+w/2) (w/2)) = form_031 := by
      funext u v w; dsimp [form_03, form_031]; ring
    rw [he]
    exact form_031_pos
  · have he : (fun u v w : ℝ => form_03 (u/2) (v/2) (u/2+v/2+w)) = form_032 := by
      funext u v w; dsimp [form_03, form_032]; ring
    rw [he]
    exact form_032_pos
  · have he : (fun u v w : ℝ => form_03 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_033 := by
      funext u v w; dsimp [form_03, form_033]; ring
    rw [he]
    exact form_033_pos

private def form_0 (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (34101 / 2 : ℝ)*u^2*v^1 + (231345 / 2 : ℝ)*u^2*w^1 + (34506 / 1 : ℝ)*u^1*v^2 + (4629861 / 4 : ℝ)*u^1*v^1*w^1 + (-16983219 / 1 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (4592277 / 8 : ℝ)*v^2*w^1 + (-50444463 / 4 : ℝ)*v^1*w^2 + (2951670013 / 8 : ℝ)*w^3

private theorem form_0_pos : ConePositive form_0 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_0 (u+v/2+w/2) (v/2) (w/2)) = form_00 := by
      funext u v w; dsimp [form_0, form_00]; ring
    rw [he]
    exact form_00_pos
  · have he : (fun u v w : ℝ => form_0 (u/2) (u/2+v+w/2) (w/2)) = form_01 := by
      funext u v w; dsimp [form_0, form_01]; ring
    rw [he]
    exact form_01_pos
  · have he : (fun u v w : ℝ => form_0 (u/2) (v/2) (u/2+v/2+w)) = form_02 := by
      funext u v w; dsimp [form_0, form_02]; ring
    rw [he]
    exact form_02_pos
  · have he : (fun u v w : ℝ => form_0 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_03 := by
      funext u v w; dsimp [form_0, form_03]; ring
    rw [he]
    exact form_03_pos

private def form_10000 (u v w : ℝ) : ℝ :=
  (13284 / 1 : ℝ)*u^3 + (321489 / 8 : ℝ)*u^2*v^1 + (9417285 / 128 : ℝ)*u^2*w^1 + (20722149 / 512 : ℝ)*u^1*v^2 + (37795905 / 256 : ℝ)*u^1*v^1*w^1 + (27430995 / 512 : ℝ)*u^1*w^2 + (111159783 / 8192 : ℝ)*v^3 + (2421706959 / 32768 : ℝ)*v^2*w^1 + (447129165 / 8192 : ℝ)*v^1*w^2 + (2868493777 / 32768 : ℝ)*w^3

private theorem form_10000_pos : ConePositive form_10000 := by
  intro u v w hu hv hw hs
  unfold form_10000
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10001 (u v w : ℝ) : ℝ :=
  (111159783 / 8192 : ℝ)*u^3 + (167702157 / 4096 : ℝ)*u^2*v^1 + (2429406819 / 32768 : ℝ)*u^2*w^1 + (84226149 / 2048 : ℝ)*u^1*v^2 + (1215238563 / 8192 : ℝ)*u^1*v^1*w^1 + (896178003 / 16384 : ℝ)*u^1*w^2 + (14080959 / 1024 : ℝ)*v^3 + (606513699 / 8192 : ℝ)*v^2*w^1 + (453613107 / 8192 : ℝ)*v^1*w^2 + (181002079 / 2048 : ℝ)*w^3

private theorem form_10001_pos : ConePositive form_10001 := by
  intro u v w hu hv hw hs
  unfold form_10001
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10002 (u v w : ℝ) : ℝ :=
  (2868493777 / 32768 : ℝ)*u^3 + (8638414311 / 32768 : ℝ)*u^2*v^1 + (7727689491 / 16384 : ℝ)*u^2*w^1 + (4333001685 / 16384 : ℝ)*u^1*v^2 + (7756565991 / 8192 : ℝ)*u^1*v^1*w^1 + (7452603891 / 8192 : ℝ)*u^1*w^2 + (181002079 / 2048 : ℝ)*v^3 + (3890436789 / 8192 : ℝ)*v^2*w^1 + (7480161063 / 8192 : ℝ)*v^1*w^2 + (2538996913 / 4096 : ℝ)*w^3

private theorem form_10002_pos : ConePositive form_10002 := by
  intro u v w hu hv hw hs
  unfold form_10002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10003 (u v w : ℝ) : ℝ :=
  (2868493777 / 32768 : ℝ)*u^3 + (447129165 / 8192 : ℝ)*u^2*v^1 + (8638414311 / 32768 : ℝ)*u^2*w^1 + (2421706959 / 32768 : ℝ)*u^1*v^2 + (1791285699 / 16384 : ℝ)*u^1*v^1*w^1 + (4333001685 / 16384 : ℝ)*u^1*w^2 + (111159783 / 8192 : ℝ)*v^3 + (2429406819 / 32768 : ℝ)*v^2*w^1 + (896178003 / 16384 : ℝ)*v^1*w^2 + (181002079 / 2048 : ℝ)*w^3

private theorem form_10003_pos : ConePositive form_10003 := by
  intro u v w hu hv hw hs
  unfold form_10003
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1000 (u v w : ℝ) : ℝ :=
  (13284 / 1 : ℝ)*u^3 + (162081 / 4 : ℝ)*u^2*v^1 + (6866757 / 64 : ℝ)*u^2*w^1 + (5247909 / 128 : ℝ)*u^1*v^2 + (13774743 / 64 : ℝ)*u^1*v^1*w^1 + (-5137089 / 128 : ℝ)*u^1*w^2 + (14080959 / 1024 : ℝ)*v^3 + (437542191 / 4096 : ℝ)*v^2*w^1 + (-34207419 / 1024 : ℝ)*v^1*w^2 + (2538996913 / 4096 : ℝ)*w^3

private theorem form_1000_pos : ConePositive form_1000 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1000 (u+v/2+w/2) (v/2) (w/2)) = form_10000 := by
      funext u v w; dsimp [form_1000, form_10000]; ring
    rw [he]
    exact form_10000_pos
  · have he : (fun u v w : ℝ => form_1000 (u/2) (u/2+v+w/2) (w/2)) = form_10001 := by
      funext u v w; dsimp [form_1000, form_10001]; ring
    rw [he]
    exact form_10001_pos
  · have he : (fun u v w : ℝ => form_1000 (u/2) (v/2) (u/2+v/2+w)) = form_10002 := by
      funext u v w; dsimp [form_1000, form_10002]; ring
    rw [he]
    exact form_10002_pos
  · have he : (fun u v w : ℝ => form_1000 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_10003 := by
      funext u v w; dsimp [form_1000, form_10003]; ring
    rw [he]
    exact form_10003_pos

private def form_10010 (u v w : ℝ) : ℝ :=
  (14080959 / 1024 : ℝ)*u^3 + (84745359 / 2048 : ℝ)*u^2*v^1 + (607552119 / 8192 : ℝ)*u^2*w^1 + (169778997 / 4096 : ℝ)*u^1*v^2 + (1211969349 / 8192 : ℝ)*u^1*v^1*w^1 + (28183755 / 512 : ℝ)*u^1*w^2 + (113211837 / 8192 : ℝ)*v^3 + (2412027567 / 32768 : ℝ)*v^2*w^1 + (28355043 / 512 : ℝ)*v^1*w^2 + (2912587477 / 32768 : ℝ)*w^3

private theorem form_10010_pos : ConePositive form_10010 := by
  intro u v w hu hv hw hs
  unfold form_10010
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10011 (u v w : ℝ) : ℝ :=
  (113211837 / 8192 : ℝ)*u^3 + (84928257 / 2048 : ℝ)*u^2*v^1 + (2412337635 / 32768 : ℝ)*u^2*w^1 + (21205719 / 512 : ℝ)*u^1*v^2 + (599607585 / 4096 : ℝ)*u^1*v^1*w^1 + (894452163 / 16384 : ℝ)*u^1*w^2 + (1762155 / 128 : ℝ)*v^3 + (148670811 / 2048 : ℝ)*v^2*w^1 + (223554417 / 4096 : ℝ)*v^1*w^2 + (364732373 / 4096 : ℝ)*w^3

private theorem form_10011_pos : ConePositive form_10011 := by
  intro u v w hu hv hw hs
  unfold form_10011
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10012 (u v w : ℝ) : ℝ :=
  (2912587477 / 32768 : ℝ)*u^3 + (8748724863 / 32768 : ℝ)*u^2*v^1 + (7835882271 / 16384 : ℝ)*u^2*w^1 + (4377022971 / 16384 : ℝ)*u^1*v^2 + (981247449 / 1024 : ℝ)*u^1*v^1*w^1 + (3770777115 / 4096 : ℝ)*u^1*w^2 + (364732373 / 4096 : ℝ)*v^3 + (1964839821 / 4096 : ℝ)*v^2*w^1 + (1889956215 / 2048 : ℝ)*v^1*w^2 + (160120975 / 256 : ℝ)*w^3

private theorem form_10012_pos : ConePositive form_10012 := by
  intro u v w hu hv hw hs
  unfold form_10012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10013 (u v w : ℝ) : ℝ :=
  (2912587477 / 32768 : ℝ)*u^3 + (28355043 / 512 : ℝ)*u^2*v^1 + (8748724863 / 32768 : ℝ)*u^2*w^1 + (2412027567 / 32768 : ℝ)*u^1*v^2 + (1802811621 / 16384 : ℝ)*u^1*v^1*w^1 + (4377022971 / 16384 : ℝ)*u^1*w^2 + (113211837 / 8192 : ℝ)*v^3 + (2412337635 / 32768 : ℝ)*v^2*w^1 + (894452163 / 16384 : ℝ)*v^1*w^2 + (364732373 / 4096 : ℝ)*w^3

private theorem form_10013_pos : ConePositive form_10013 := by
  intro u v w hu hv hw hs
  unfold form_10013
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1001 (u v w : ℝ) : ℝ :=
  (14080959 / 1024 : ℝ)*u^3 + (21251241 / 512 : ℝ)*u^2*v^1 + (438580611 / 4096 : ℝ)*u^2*w^1 + (10632789 / 256 : ℝ)*u^1*v^2 + (217203651 / 1024 : ℝ)*u^1*v^1*w^1 + (-72126285 / 2048 : ℝ)*u^1*w^2 + (1762155 / 128 : ℝ)*v^3 + (106379091 / 1024 : ℝ)*v^2*w^1 + (-31495485 / 1024 : ℝ)*v^1*w^2 + (160120975 / 256 : ℝ)*w^3

private theorem form_1001_pos : ConePositive form_1001 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1001 (u+v/2+w/2) (v/2) (w/2)) = form_10010 := by
      funext u v w; dsimp [form_1001, form_10010]; ring
    rw [he]
    exact form_10010_pos
  · have he : (fun u v w : ℝ => form_1001 (u/2) (u/2+v+w/2) (w/2)) = form_10011 := by
      funext u v w; dsimp [form_1001, form_10011]; ring
    rw [he]
    exact form_10011_pos
  · have he : (fun u v w : ℝ => form_1001 (u/2) (v/2) (u/2+v/2+w)) = form_10012 := by
      funext u v w; dsimp [form_1001, form_10012]; ring
    rw [he]
    exact form_10012_pos
  · have he : (fun u v w : ℝ => form_1001 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_10013 := by
      funext u v w; dsimp [form_1001, form_10013]; ring
    rw [he]
    exact form_10013_pos

private def form_1002 (u v w : ℝ) : ℝ :=
  (2538996913 / 4096 : ℝ)*u^3 + (7644547911 / 4096 : ℝ)*u^2*v^1 + (7699184163 / 2048 : ℝ)*u^2*w^1 + (3833768085 / 2048 : ℝ)*u^1*v^2 + (7726081671 / 1024 : ℝ)*u^1*v^1*w^1 + (7891245699 / 1024 : ℝ)*u^1*w^2 + (160120975 / 256 : ℝ)*v^3 + (3874398885 / 1024 : ℝ)*v^2*w^1 + (7918167831 / 1024 : ℝ)*v^1*w^2 + (2724257041 / 512 : ℝ)*w^3

private theorem form_1002_pos : ConePositive form_1002 := by
  intro u v w hu hv hw hs
  unfold form_1002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10030 (u v w : ℝ) : ℝ :=
  (2538996913 / 4096 : ℝ)*u^3 + (7480161063 / 8192 : ℝ)*u^2*v^1 + (7630769325 / 4096 : ℝ)*u^2*w^1 + (3890436789 / 8192 : ℝ)*u^1*v^2 + (14984629713 / 8192 : ℝ)*u^1*v^1*w^1 + (30573622731 / 16384 : ℝ)*u^1*w^2 + (181002079 / 2048 : ℝ)*v^3 + (7791921789 / 16384 : ℝ)*v^2*w^1 + (30012381963 / 32768 : ℝ)*v^1*w^2 + (10206508297 / 16384 : ℝ)*w^3

private theorem form_10030_pos : ConePositive form_10030 := by
  intro u v w hu hv hw hs
  unfold form_10030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10031 (u v w : ℝ) : ℝ :=
  (181002079 / 2048 : ℝ)*u^3 + (453613107 / 8192 : ℝ)*u^2*v^1 + (4355098107 / 16384 : ℝ)*u^2*w^1 + (606513699 / 8192 : ℝ)*u^1*v^2 + (905015049 / 8192 : ℝ)*u^1*v^1*w^1 + (8726799999 / 32768 : ℝ)*u^1*w^2 + (14080959 / 1024 : ℝ)*v^3 + (607552119 / 8192 : ℝ)*v^2*w^1 + (28183755 / 512 : ℝ)*v^1*w^2 + (2912587477 / 32768 : ℝ)*w^3

private theorem form_10031_pos : ConePositive form_10031 := by
  intro u v w hu hv hw hs
  unfold form_10031
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10032 (u v w : ℝ) : ℝ :=
  (10206508297 / 16384 : ℝ)*u^3 + (30104186283 / 32768 : ℝ)*u^2*v^1 + (30665427051 / 16384 : ℝ)*u^2*w^1 + (7830401055 / 16384 : ℝ)*u^1*v^2 + (15069011139 / 8192 : ℝ)*u^1*v^1*w^1 + (7676671485 / 4096 : ℝ)*u^1*w^2 + (2912587477 / 32768 : ℝ)*v^3 + (7835882271 / 16384 : ℝ)*v^2*w^1 + (3770777115 / 4096 : ℝ)*v^1*w^2 + (160120975 / 256 : ℝ)*w^3

private theorem form_10032_pos : ConePositive form_10032 := by
  intro u v w hu hv hw hs
  unfold form_10032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10033 (u v w : ℝ) : ℝ :=
  (10206508297 / 16384 : ℝ)*u^3 + (30012381963 / 32768 : ℝ)*u^2*v^1 + (30104186283 / 32768 : ℝ)*u^2*w^1 + (7791921789 / 16384 : ℝ)*u^1*v^2 + (15626966115 / 16384 : ℝ)*u^1*v^1*w^1 + (7830401055 / 16384 : ℝ)*u^1*w^2 + (181002079 / 2048 : ℝ)*v^3 + (4355098107 / 16384 : ℝ)*v^2*w^1 + (8726799999 / 32768 : ℝ)*v^1*w^2 + (2912587477 / 32768 : ℝ)*w^3

private theorem form_10033_pos : ConePositive form_10033 := by
  intro u v w hu hv hw hs
  unfold form_10033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1003 (u v w : ℝ) : ℝ :=
  (2538996913 / 4096 : ℝ)*u^3 + (-34207419 / 1024 : ℝ)*u^2*v^1 + (7644547911 / 4096 : ℝ)*u^2*w^1 + (437542191 / 4096 : ℝ)*u^1*v^2 + (-140079261 / 2048 : ℝ)*u^1*v^1*w^1 + (3833768085 / 2048 : ℝ)*u^1*w^2 + (14080959 / 1024 : ℝ)*v^3 + (438580611 / 4096 : ℝ)*v^2*w^1 + (-72126285 / 2048 : ℝ)*v^1*w^2 + (160120975 / 256 : ℝ)*w^3

private theorem form_1003_pos : ConePositive form_1003 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1003 (u+v/2+w/2) (v/2) (w/2)) = form_10030 := by
      funext u v w; dsimp [form_1003, form_10030]; ring
    rw [he]
    exact form_10030_pos
  · have he : (fun u v w : ℝ => form_1003 (u/2) (u/2+v+w/2) (w/2)) = form_10031 := by
      funext u v w; dsimp [form_1003, form_10031]; ring
    rw [he]
    exact form_10031_pos
  · have he : (fun u v w : ℝ => form_1003 (u/2) (v/2) (u/2+v/2+w)) = form_10032 := by
      funext u v w; dsimp [form_1003, form_10032]; ring
    rw [he]
    exact form_10032_pos
  · have he : (fun u v w : ℝ => form_1003 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_10033 := by
      funext u v w; dsimp [form_1003, form_10033]; ring
    rw [he]
    exact form_10033_pos

private def form_100 (u v w : ℝ) : ℝ :=
  (13284 / 1 : ℝ)*u^3 + (82377 / 2 : ℝ)*u^2*v^1 + (5591493 / 32 : ℝ)*u^2*w^1 + (1336581 / 32 : ℝ)*u^1*v^2 + (2794977 / 8 : ℝ)*u^1*v^1*w^1 + (-17595339 / 32 : ℝ)*u^1*w^2 + (1762155 / 128 : ℝ)*v^3 + (85233231 / 512 : ℝ)*v^2*w^1 + (-63650823 / 128 : ℝ)*v^1*w^2 + (2724257041 / 512 : ℝ)*w^3

private theorem form_100_pos : ConePositive form_100 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_100 (u+v/2+w/2) (v/2) (w/2)) = form_1000 := by
      funext u v w; dsimp [form_100, form_1000]; ring
    rw [he]
    exact form_1000_pos
  · have he : (fun u v w : ℝ => form_100 (u/2) (u/2+v+w/2) (w/2)) = form_1001 := by
      funext u v w; dsimp [form_100, form_1001]; ring
    rw [he]
    exact form_1001_pos
  · have he : (fun u v w : ℝ => form_100 (u/2) (v/2) (u/2+v/2+w)) = form_1002 := by
      funext u v w; dsimp [form_100, form_1002]; ring
    rw [he]
    exact form_1002_pos
  · have he : (fun u v w : ℝ => form_100 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1003 := by
      funext u v w; dsimp [form_100, form_1003]; ring
    rw [he]
    exact form_1003_pos

private def form_10100 (u v w : ℝ) : ℝ :=
  (1762155 / 128 : ℝ)*u^3 + (21086001 / 512 : ℝ)*u^2*v^1 + (148431375 / 2048 : ℝ)*u^2*w^1 + (83970513 / 2048 : ℝ)*u^1*v^2 + (588264939 / 4096 : ℝ)*u^1*v^1*w^1 + (109180983 / 2048 : ℝ)*u^1*w^2 + (111271563 / 8192 : ℝ)*v^3 + (2325278727 / 32768 : ℝ)*v^2*w^1 + (433674471 / 8192 : ℝ)*v^1*w^2 + (2911550353 / 32768 : ℝ)*w^3

private theorem form_10100_pos : ConePositive form_10100 := by
  intro u v w hu hv hw hs
  unfold form_10100
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10101 (u v w : ℝ) : ℝ :=
  (111271563 / 8192 : ℝ)*u^3 + (165873663 / 4096 : ℝ)*u^2*v^1 + (2317009275 / 32768 : ℝ)*u^2*w^1 + (82276641 / 2048 : ℝ)*u^1*v^2 + (1143467325 / 8192 : ℝ)*u^1*v^1*w^1 + (838421115 / 16384 : ℝ)*u^1*w^2 + (13577301 / 1024 : ℝ)*v^3 + (562693131 / 8192 : ℝ)*v^2*w^1 + (413154525 / 8192 : ℝ)*v^1*w^2 + (361670519 / 4096 : ℝ)*w^3

private theorem form_10101_pos : ConePositive form_10101 := by
  intro u v w hu hv hw hs
  unfold form_10101
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10102 (u v w : ℝ) : ℝ :=
  (2911550353 / 32768 : ℝ)*u^3 + (8722453215 / 32768 : ℝ)*u^2*v^1 + (7861203195 / 16384 : ℝ)*u^2*w^1 + (4352158293 / 16384 : ℝ)*u^1*v^2 + (7859926473 / 8192 : ℝ)*u^1*v^1*w^1 + (7581480831 / 8192 : ℝ)*u^1*w^2 + (361670519 / 4096 : ℝ)*v^3 + (3926891703 / 8192 : ℝ)*v^2*w^1 + (7590167487 / 8192 : ℝ)*v^1*w^2 + (2575439029 / 4096 : ℝ)*w^3

private theorem form_10102_pos : ConePositive form_10102 := by
  intro u v w hu hv hw hs
  unfold form_10102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10103 (u v w : ℝ) : ℝ :=
  (2911550353 / 32768 : ℝ)*u^3 + (433674471 / 8192 : ℝ)*u^2*v^1 + (8722453215 / 32768 : ℝ)*u^2*w^1 + (2325278727 / 32768 : ℝ)*u^1*v^2 + (1706916855 / 16384 : ℝ)*u^1*v^1*w^1 + (4352158293 / 16384 : ℝ)*u^1*w^2 + (111271563 / 8192 : ℝ)*v^3 + (2317009275 / 32768 : ℝ)*v^2*w^1 + (838421115 / 16384 : ℝ)*v^1*w^2 + (361670519 / 4096 : ℝ)*w^3

private theorem form_10103_pos : ConePositive form_10103 := by
  intro u v w hu hv hw hs
  unfold form_10103
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1010 (u v w : ℝ) : ℝ :=
  (1762155 / 128 : ℝ)*u^3 + (10513071 / 256 : ℝ)*u^2*v^1 + (106139655 / 1024 : ℝ)*u^2*w^1 + (20772369 / 512 : ℝ)*u^1*v^2 + (207297621 / 1024 : ℝ)*u^1*v^1*w^1 + (-4526133 / 128 : ℝ)*u^1*w^2 + (13577301 / 1024 : ℝ)*v^3 + (399765519 / 4096 : ℝ)*v^2*w^1 + (-4254675 / 128 : ℝ)*v^1*w^2 + (2575439029 / 4096 : ℝ)*w^3

private theorem form_1010_pos : ConePositive form_1010 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1010 (u+v/2+w/2) (v/2) (w/2)) = form_10100 := by
      funext u v w; dsimp [form_1010, form_10100]; ring
    rw [he]
    exact form_10100_pos
  · have he : (fun u v w : ℝ => form_1010 (u/2) (u/2+v+w/2) (w/2)) = form_10101 := by
      funext u v w; dsimp [form_1010, form_10101]; ring
    rw [he]
    exact form_10101_pos
  · have he : (fun u v w : ℝ => form_1010 (u/2) (v/2) (u/2+v/2+w)) = form_10102 := by
      funext u v w; dsimp [form_1010, form_10102]; ring
    rw [he]
    exact form_10102_pos
  · have he : (fun u v w : ℝ => form_1010 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_10103 := by
      funext u v w; dsimp [form_1010, form_10103]; ring
    rw [he]
    exact form_10103_pos

private def form_10110 (u v w : ℝ) : ℝ :=
  (13577301 / 1024 : ℝ)*u^3 + (80650971 / 2048 : ℝ)*u^2*v^1 + (559441791 / 8192 : ℝ)*u^2*w^1 + (159370983 / 4096 : ℝ)*u^1*v^2 + (1099581363 / 8192 : ℝ)*u^1*v^1*w^1 + (98615721 / 2048 : ℝ)*u^1*w^2 + (104744097 / 8192 : ℝ)*v^3 + (2154322071 / 32768 : ℝ)*v^2*w^1 + (192662961 / 4096 : ℝ)*v^1*w^2 + (2863002949 / 32768 : ℝ)*w^3

private theorem form_10110_pos : ConePositive form_10110 := by
  intro u v w hu hv hw hs
  unfold form_10110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10111 (u v w : ℝ) : ℝ :=
  (104744097 / 8192 : ℝ)*u^3 + (38715327 / 1024 : ℝ)*u^2*v^1 + (2136283371 / 32768 : ℝ)*u^2*w^1 + (4758831 / 128 : ℝ)*u^1*v^2 + (261106461 / 2048 : ℝ)*u^1*v^1*w^1 + (724515675 / 16384 : ℝ)*u^1*w^2 + (194481 / 16 : ℝ)*v^3 + (31797423 / 512 : ℝ)*v^2*w^1 + (87491397 / 2048 : ℝ)*v^1*w^2 + (88130291 / 1024 : ℝ)*w^3

private theorem form_10111_pos : ConePositive form_10111 := by
  intro u v w hu hv hw hs
  unfold form_10111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10112 (u v w : ℝ) : ℝ :=
  (2863002949 / 32768 : ℝ)*u^3 + (8552460999 / 32768 : ℝ)*u^2*v^1 + (7800083079 / 16384 : ℝ)*u^2*w^1 + (4254838467 / 16384 : ℝ)*u^1*v^2 + (3891418725 / 4096 : ℝ)*u^1*v^1*w^1 + (3785299551 / 4096 : ℝ)*u^1*w^2 + (88130291 / 1024 : ℝ)*v^3 + (970072095 / 2048 : ℝ)*v^2*w^1 + (118271943 / 128 : ℝ)*v^1*w^2 + (322401221 / 512 : ℝ)*w^3

private theorem form_10112_pos : ConePositive form_10112 := by
  intro u v w hu hv hw hs
  unfold form_10112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10113 (u v w : ℝ) : ℝ :=
  (2863002949 / 32768 : ℝ)*u^3 + (192662961 / 4096 : ℝ)*u^2*v^1 + (8552460999 / 32768 : ℝ)*u^2*w^1 + (2154322071 / 32768 : ℝ)*u^1*v^2 + (1496463033 / 16384 : ℝ)*u^1*v^1*w^1 + (4254838467 / 16384 : ℝ)*u^1*w^2 + (104744097 / 8192 : ℝ)*v^3 + (2136283371 / 32768 : ℝ)*v^2*w^1 + (724515675 / 16384 : ℝ)*v^1*w^2 + (88130291 / 1024 : ℝ)*w^3

private theorem form_10113_pos : ConePositive form_10113 := by
  intro u v w hu hv hw hs
  unfold form_10113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1011 (u v w : ℝ) : ℝ :=
  (13577301 / 1024 : ℝ)*u^3 + (9979767 / 256 : ℝ)*u^2*v^1 + (396514179 / 4096 : ℝ)*u^2*w^1 + (2425059 / 64 : ℝ)*u^1*v^2 + (95115825 / 512 : ℝ)*u^1*v^1*w^1 + (-83515101 / 2048 : ℝ)*u^1*w^2 + (194481 / 16 : ℝ)*v^3 + (22462335 / 256 : ℝ)*v^2*w^1 + (-21028119 / 512 : ℝ)*v^1*w^2 + (322401221 / 512 : ℝ)*w^3

private theorem form_1011_pos : ConePositive form_1011 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1011 (u+v/2+w/2) (v/2) (w/2)) = form_10110 := by
      funext u v w; dsimp [form_1011, form_10110]; ring
    rw [he]
    exact form_10110_pos
  · have he : (fun u v w : ℝ => form_1011 (u/2) (u/2+v+w/2) (w/2)) = form_10111 := by
      funext u v w; dsimp [form_1011, form_10111]; ring
    rw [he]
    exact form_10111_pos
  · have he : (fun u v w : ℝ => form_1011 (u/2) (v/2) (u/2+v/2+w)) = form_10112 := by
      funext u v w; dsimp [form_1011, form_10112]; ring
    rw [he]
    exact form_10112_pos
  · have he : (fun u v w : ℝ => form_1011 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_10113 := by
      funext u v w; dsimp [form_1011, form_10113]; ring
    rw [he]
    exact form_10113_pos

private def form_1012 (u v w : ℝ) : ℝ :=
  (2575439029 / 4096 : ℝ)*u^3 + (7735003743 / 4096 : ℝ)*u^2*v^1 + (7798735215 / 2048 : ℝ)*u^2*w^1 + (3869412027 / 2048 : ℝ)*u^1*v^2 + (976550445 / 128 : ℝ)*u^1*v^1*w^1 + (3988646499 / 512 : ℝ)*u^1*w^2 + (322401221 / 512 : ℝ)*v^3 + (1955435445 / 512 : ℝ)*v^2*w^1 + (1998925899 / 256 : ℝ)*v^1*w^2 + (85842131 / 16 : ℝ)*w^3

private theorem form_1012_pos : ConePositive form_1012 := by
  intro u v w hu hv hw hs
  unfold form_1012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10130 (u v w : ℝ) : ℝ :=
  (2575439029 / 4096 : ℝ)*u^3 + (7590167487 / 8192 : ℝ)*u^2*v^1 + (7730660415 / 4096 : ℝ)*u^2*w^1 + (3926891703 / 8192 : ℝ)*u^1*v^2 + (15174191907 / 8192 : ℝ)*u^1*v^1*w^1 + (30935148627 / 16384 : ℝ)*u^1*w^2 + (361670519 / 4096 : ℝ)*v^3 + (7841671341 / 16384 : ℝ)*v^2*w^1 + (30330010179 / 32768 : ℝ)*v^1*w^2 + (10314238297 / 16384 : ℝ)*w^3

private theorem form_10130_pos : ConePositive form_10130 := by
  intro u v w hu hv hw hs
  unfold form_10130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10131 (u v w : ℝ) : ℝ :=
  (361670519 / 4096 : ℝ)*u^3 + (413154525 / 8192 : ℝ)*u^2*v^1 + (4327934163 / 16384 : ℝ)*u^2*w^1 + (562693131 / 8192 : ℝ)*u^1*v^2 + (808227987 / 8192 : ℝ)*u^1*v^1*w^1 + (8625556695 / 32768 : ℝ)*u^1*w^2 + (13577301 / 1024 : ℝ)*v^3 + (559441791 / 8192 : ℝ)*v^2*w^1 + (98615721 / 2048 : ℝ)*v^1*w^2 + (2863002949 / 32768 : ℝ)*w^3

private theorem form_10131_pos : ConePositive form_10131 := by
  intro u v w hu hv hw hs
  unfold form_10131
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10132 (u v w : ℝ) : ℝ :=
  (10314238297 / 16384 : ℝ)*u^3 + (30345142707 / 32768 : ℝ)*u^2*v^1 + (30950281155 / 16384 : ℝ)*u^2*w^1 + (7818357003 / 16384 : ℝ)*u^1*v^2 + (15158443833 / 8192 : ℝ)*u^1*v^1*w^1 + (7738226679 / 4096 : ℝ)*u^1*w^2 + (2863002949 / 32768 : ℝ)*v^3 + (7800083079 / 16384 : ℝ)*v^2*w^1 + (3785299551 / 4096 : ℝ)*v^1*w^2 + (322401221 / 512 : ℝ)*w^3

private theorem form_10132_pos : ConePositive form_10132 := by
  intro u v w hu hv hw hs
  unfold form_10132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10133 (u v w : ℝ) : ℝ :=
  (10314238297 / 16384 : ℝ)*u^3 + (30330010179 / 32768 : ℝ)*u^2*v^1 + (30345142707 / 32768 : ℝ)*u^2*w^1 + (7841671341 / 16384 : ℝ)*u^1*v^2 + (15664969047 / 16384 : ℝ)*u^1*v^1*w^1 + (7818357003 / 16384 : ℝ)*u^1*w^2 + (361670519 / 4096 : ℝ)*v^3 + (4327934163 / 16384 : ℝ)*v^2*w^1 + (8625556695 / 32768 : ℝ)*v^1*w^2 + (2863002949 / 32768 : ℝ)*w^3

private theorem form_10133_pos : ConePositive form_10133 := by
  intro u v w hu hv hw hs
  unfold form_10133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1013 (u v w : ℝ) : ℝ :=
  (2575439029 / 4096 : ℝ)*u^3 + (-4254675 / 128 : ℝ)*u^2*v^1 + (7735003743 / 4096 : ℝ)*u^2*w^1 + (399765519 / 4096 : ℝ)*u^1*v^2 + (-150979323 / 2048 : ℝ)*u^1*v^1*w^1 + (3869412027 / 2048 : ℝ)*u^1*w^2 + (13577301 / 1024 : ℝ)*v^3 + (396514179 / 4096 : ℝ)*v^2*w^1 + (-83515101 / 2048 : ℝ)*v^1*w^2 + (322401221 / 512 : ℝ)*w^3

private theorem form_1013_pos : ConePositive form_1013 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1013 (u+v/2+w/2) (v/2) (w/2)) = form_10130 := by
      funext u v w; dsimp [form_1013, form_10130]; ring
    rw [he]
    exact form_10130_pos
  · have he : (fun u v w : ℝ => form_1013 (u/2) (u/2+v+w/2) (w/2)) = form_10131 := by
      funext u v w; dsimp [form_1013, form_10131]; ring
    rw [he]
    exact form_10131_pos
  · have he : (fun u v w : ℝ => form_1013 (u/2) (v/2) (u/2+v/2+w)) = form_10132 := by
      funext u v w; dsimp [form_1013, form_10132]; ring
    rw [he]
    exact form_10132_pos
  · have he : (fun u v w : ℝ => form_1013 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_10133 := by
      funext u v w; dsimp [form_1013, form_10133]; ring
    rw [he]
    exact form_10133_pos

private def form_101 (u v w : ℝ) : ℝ :=
  (1762155 / 128 : ℝ)*u^3 + (2613303 / 64 : ℝ)*u^2*v^1 + (84993795 / 512 : ℝ)*u^2*w^1 + (1258173 / 32 : ℝ)*u^1*v^2 + (40125771 / 128 : ℝ)*u^1*v^1*w^1 + (-131775789 / 256 : ℝ)*u^1*w^2 + (194481 / 16 : ℝ)*v^3 + (17794791 / 128 : ℝ)*v^2*w^1 + (-61285245 / 128 : ℝ)*v^1*w^2 + (85842131 / 16 : ℝ)*w^3

private theorem form_101_pos : ConePositive form_101 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_101 (u+v/2+w/2) (v/2) (w/2)) = form_1010 := by
      funext u v w; dsimp [form_101, form_1010]; ring
    rw [he]
    exact form_1010_pos
  · have he : (fun u v w : ℝ => form_101 (u/2) (u/2+v+w/2) (w/2)) = form_1011 := by
      funext u v w; dsimp [form_101, form_1011]; ring
    rw [he]
    exact form_1011_pos
  · have he : (fun u v w : ℝ => form_101 (u/2) (v/2) (u/2+v/2+w)) = form_1012 := by
      funext u v w; dsimp [form_101, form_1012]; ring
    rw [he]
    exact form_1012_pos
  · have he : (fun u v w : ℝ => form_101 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1013 := by
      funext u v w; dsimp [form_101, form_1013]; ring
    rw [he]
    exact form_1013_pos

private def form_102 (u v w : ℝ) : ℝ :=
  (2724257041 / 512 : ℝ)*u^3 + (8199693255 / 512 : ℝ)*u^2*v^1 + (8313533835 / 256 : ℝ)*u^2*w^1 + (4111216989 / 256 : ℝ)*u^1*v^2 + (8340468279 / 128 : ℝ)*u^1*v^1*w^1 + (8476662519 / 128 : ℝ)*u^1*w^2 + (85842131 / 16 : ℝ)*v^3 + (4181707533 / 128 : ℝ)*v^2*w^1 + (8503780347 / 128 : ℝ)*v^1*w^2 + (2886535549 / 64 : ℝ)*w^3

private theorem form_102_pos : ConePositive form_102 := by
  intro u v w hu hv hw hs
  unfold form_102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1030 (u v w : ℝ) : ℝ :=
  (2724257041 / 512 : ℝ)*u^3 + (7918167831 / 1024 : ℝ)*u^2*v^1 + (8186232189 / 512 : ℝ)*u^2*w^1 + (3874398885 / 1024 : ℝ)*u^1*v^2 + (15859051761 / 1024 : ℝ)*u^1*v^1*w^1 + (32794591611 / 2048 : ℝ)*u^1*w^2 + (160120975 / 256 : ℝ)*v^3 + (7757933085 / 2048 : ℝ)*v^2*w^1 + (31758818091 / 4096 : ℝ)*v^1*w^2 + (10946666233 / 2048 : ℝ)*w^3

private theorem form_1030_pos : ConePositive form_1030 := by
  intro u v w hu hv hw hs
  unfold form_1030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10310 (u v w : ℝ) : ℝ :=
  (160120975 / 256 : ℝ)*u^3 + (1889956215 / 2048 : ℝ)*u^2*v^1 + (7694942115 / 4096 : ℝ)*u^2*w^1 + (1964839821 / 4096 : ℝ)*u^1*v^2 + (3782257353 / 2048 : ℝ)*u^1*v^1*w^1 + (30811592091 / 16384 : ℝ)*u^1*w^2 + (364732373 / 4096 : ℝ)*v^3 + (7859124789 / 16384 : ℝ)*v^2*w^1 + (30271028139 / 32768 : ℝ)*v^1*w^2 + (10279541245 / 16384 : ℝ)*w^3

private theorem form_10310_pos : ConePositive form_10310 := by
  intro u v w hu hv hw hs
  unfold form_10310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10311 (u v w : ℝ) : ℝ :=
  (364732373 / 4096 : ℝ)*u^3 + (223554417 / 4096 : ℝ)*u^2*v^1 + (4376553981 / 16384 : ℝ)*u^2*w^1 + (148670811 / 2048 : ℝ)*u^1*v^2 + (442184493 / 4096 : ℝ)*u^1*v^1*w^1 + (8746848903 / 32768 : ℝ)*u^1*w^2 + (1762155 / 128 : ℝ)*v^3 + (148431375 / 2048 : ℝ)*v^2*w^1 + (109180983 / 2048 : ℝ)*v^1*w^2 + (2911550353 / 32768 : ℝ)*w^3

private theorem form_10311_pos : ConePositive form_10311 := by
  intro u v w hu hv hw hs
  unfold form_10311
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10312 (u v w : ℝ) : ℝ :=
  (10279541245 / 16384 : ℝ)*u^3 + (30325091427 / 32768 : ℝ)*u^2*v^1 + (30865655379 / 16384 : ℝ)*u^2*w^1 + (7867302117 / 16384 : ℝ)*u^1*v^2 + (947764899 / 512 : ℝ)*u^1*v^1*w^1 + (7721973759 / 4096 : ℝ)*u^1*w^2 + (2911550353 / 32768 : ℝ)*v^3 + (7861203195 / 16384 : ℝ)*v^2*w^1 + (7581480831 / 8192 : ℝ)*v^1*w^2 + (2575439029 / 4096 : ℝ)*w^3

private theorem form_10312_pos : ConePositive form_10312 := by
  intro u v w hu hv hw hs
  unfold form_10312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_10313 (u v w : ℝ) : ℝ :=
  (10279541245 / 16384 : ℝ)*u^3 + (30271028139 / 32768 : ℝ)*u^2*v^1 + (30325091427 / 32768 : ℝ)*u^2*w^1 + (7859124789 / 16384 : ℝ)*u^1*v^2 + (15731218893 / 16384 : ℝ)*u^1*v^1*w^1 + (7867302117 / 16384 : ℝ)*u^1*w^2 + (364732373 / 4096 : ℝ)*v^3 + (4376553981 / 16384 : ℝ)*v^2*w^1 + (8746848903 / 32768 : ℝ)*v^1*w^2 + (2911550353 / 32768 : ℝ)*w^3

private theorem form_10313_pos : ConePositive form_10313 := by
  intro u v w hu hv hw hs
  unfold form_10313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1031 (u v w : ℝ) : ℝ :=
  (160120975 / 256 : ℝ)*u^3 + (-31495485 / 1024 : ℝ)*u^2*v^1 + (3852038715 / 2048 : ℝ)*u^2*w^1 + (106379091 / 1024 : ℝ)*u^1*v^2 + (-67436439 / 1024 : ℝ)*u^1*v^1*w^1 + (7717630431 / 4096 : ℝ)*u^1*w^2 + (1762155 / 128 : ℝ)*v^3 + (106139655 / 1024 : ℝ)*v^2*w^1 + (-4526133 / 128 : ℝ)*v^1*w^2 + (2575439029 / 4096 : ℝ)*w^3

private theorem form_1031_pos : ConePositive form_1031 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1031 (u+v/2+w/2) (v/2) (w/2)) = form_10310 := by
      funext u v w; dsimp [form_1031, form_10310]; ring
    rw [he]
    exact form_10310_pos
  · have he : (fun u v w : ℝ => form_1031 (u/2) (u/2+v+w/2) (w/2)) = form_10311 := by
      funext u v w; dsimp [form_1031, form_10311]; ring
    rw [he]
    exact form_10311_pos
  · have he : (fun u v w : ℝ => form_1031 (u/2) (v/2) (u/2+v/2+w)) = form_10312 := by
      funext u v w; dsimp [form_1031, form_10312]; ring
    rw [he]
    exact form_10312_pos
  · have he : (fun u v w : ℝ => form_1031 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_10313 := by
      funext u v w; dsimp [form_1031, form_10313]; ring
    rw [he]
    exact form_10313_pos

private def form_1032 (u v w : ℝ) : ℝ :=
  (10946666233 / 2048 : ℝ)*u^3 + (31849632267 / 4096 : ℝ)*u^2*v^1 + (32885405787 / 2048 : ℝ)*u^2*w^1 + (7794391887 / 2048 : ℝ)*u^1*v^2 + (15940917651 / 1024 : ℝ)*u^1*v^1*w^1 + (8231639277 / 512 : ℝ)*u^1*w^2 + (2575439029 / 4096 : ℝ)*v^3 + (7798735215 / 2048 : ℝ)*v^2*w^1 + (3988646499 / 512 : ℝ)*v^1*w^2 + (85842131 / 16 : ℝ)*w^3

private theorem form_1032_pos : ConePositive form_1032 := by
  intro u v w hu hv hw hs
  unfold form_1032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1033 (u v w : ℝ) : ℝ :=
  (10946666233 / 2048 : ℝ)*u^3 + (31758818091 / 4096 : ℝ)*u^2*v^1 + (31849632267 / 4096 : ℝ)*u^2*w^1 + (7757933085 / 2048 : ℝ)*u^1*v^2 + (15556580739 / 2048 : ℝ)*u^1*v^1*w^1 + (7794391887 / 2048 : ℝ)*u^1*w^2 + (160120975 / 256 : ℝ)*v^3 + (3852038715 / 2048 : ℝ)*v^2*w^1 + (7717630431 / 4096 : ℝ)*v^1*w^2 + (2575439029 / 4096 : ℝ)*w^3

private theorem form_1033_pos : ConePositive form_1033 := by
  intro u v w hu hv hw hs
  unfold form_1033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_103 (u v w : ℝ) : ℝ :=
  (2724257041 / 512 : ℝ)*u^3 + (-63650823 / 128 : ℝ)*u^2*v^1 + (8199693255 / 512 : ℝ)*u^2*w^1 + (85233231 / 512 : ℝ)*u^1*v^2 + (-258809325 / 256 : ℝ)*u^1*v^1*w^1 + (4111216989 / 256 : ℝ)*u^1*w^2 + (1762155 / 128 : ℝ)*v^3 + (84993795 / 512 : ℝ)*v^2*w^1 + (-131775789 / 256 : ℝ)*v^1*w^2 + (85842131 / 16 : ℝ)*w^3

private theorem form_103_pos : ConePositive form_103 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_103 (u+v/2+w/2) (v/2) (w/2)) = form_1030 := by
      funext u v w; dsimp [form_103, form_1030]; ring
    rw [he]
    exact form_1030_pos
  · have he : (fun u v w : ℝ => form_103 (u/2) (u/2+v+w/2) (w/2)) = form_1031 := by
      funext u v w; dsimp [form_103, form_1031]; ring
    rw [he]
    exact form_1031_pos
  · have he : (fun u v w : ℝ => form_103 (u/2) (v/2) (u/2+v/2+w)) = form_1032 := by
      funext u v w; dsimp [form_103, form_1032]; ring
    rw [he]
    exact form_1032_pos
  · have he : (fun u v w : ℝ => form_103 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1033 := by
      funext u v w; dsimp [form_103, form_1033]; ring
    rw [he]
    exact form_1033_pos

private def form_10 (u v w : ℝ) : ℝ :=
  (13284 / 1 : ℝ)*u^3 + (42525 / 1 : ℝ)*u^2*v^1 + (4953861 / 16 : ℝ)*u^2*w^1 + (337365 / 8 : ℝ)*u^1*v^2 + (4908015 / 8 : ℝ)*u^1*v^1*w^1 + (-2858502 / 1 : ℝ)*u^1*w^2 + (194481 / 16 : ℝ)*v^3 + (15461019 / 64 : ℝ)*v^2*w^1 + (-38956575 / 16 : ℝ)*v^1*w^2 + (2886535549 / 64 : ℝ)*w^3

private theorem form_10_pos : ConePositive form_10 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_10 (u+v/2+w/2) (v/2) (w/2)) = form_100 := by
      funext u v w; dsimp [form_10, form_100]; ring
    rw [he]
    exact form_100_pos
  · have he : (fun u v w : ℝ => form_10 (u/2) (u/2+v+w/2) (w/2)) = form_101 := by
      funext u v w; dsimp [form_10, form_101]; ring
    rw [he]
    exact form_101_pos
  · have he : (fun u v w : ℝ => form_10 (u/2) (v/2) (u/2+v/2+w)) = form_102 := by
      funext u v w; dsimp [form_10, form_102]; ring
    rw [he]
    exact form_102_pos
  · have he : (fun u v w : ℝ => form_10 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_103 := by
      funext u v w; dsimp [form_10, form_103]; ring
    rw [he]
    exact form_103_pos

private def form_11000 (u v w : ℝ) : ℝ :=
  (194481 / 16 : ℝ)*u^3 + (4576257 / 128 : ℝ)*u^2*v^1 + (31432275 / 512 : ℝ)*u^2*w^1 + (35794143 / 1024 : ℝ)*u^1*v^2 + (244388655 / 2048 : ℝ)*u^1*v^1*w^1 + (40296543 / 1024 : ℝ)*u^1*w^2 + (93034575 / 8192 : ℝ)*v^3 + (1892019231 / 32768 : ℝ)*v^2*w^1 + (306850449 / 8192 : ℝ)*v^1*w^2 + (2764565809 / 32768 : ℝ)*w^3

private theorem form_11000_pos : ConePositive form_11000 := by
  intro u v w hu hv hw hs
  unfold form_11000
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11001 (u v w : ℝ) : ℝ :=
  (93034575 / 8192 : ℝ)*u^3 + (135927153 / 4096 : ℝ)*u^2*v^1 + (1863021555 / 32768 : ℝ)*u^2*w^1 + (65970693 / 2048 : ℝ)*u^1*v^2 + (898521543 / 8192 : ℝ)*u^1*v^1*w^1 + (549166659 / 16384 : ℝ)*u^1*w^2 + (10631331 / 1024 : ℝ)*v^3 + (431095563 / 8192 : ℝ)*v^2*w^1 + (255757431 / 8192 : ℝ)*v^1*w^2 + (84246719 / 1024 : ℝ)*w^3

private theorem form_11001_pos : ConePositive form_11001 := by
  intro u v w hu hv hw hs
  unfold form_11001
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11002 (u v w : ℝ) : ℝ :=
  (2764565809 / 32768 : ℝ)*u^3 + (8231609847 / 32768 : ℝ)*u^2*v^1 + (7648952739 / 16384 : ℝ)*u^2*w^1 + (4081494309 / 16384 : ℝ)*u^1*v^2 + (7615143339 / 8192 : ℝ)*u^1*v^1*w^1 + (7507124451 / 8192 : ℝ)*u^1*w^2 + (84246719 / 1024 : ℝ)*v^3 + (3788085081 / 8192 : ℝ)*v^2*w^1 + (7495750863 / 8192 : ℝ)*v^1*w^2 + (2572950385 / 4096 : ℝ)*w^3

private theorem form_11002_pos : ConePositive form_11002 := by
  intro u v w hu hv hw hs
  unfold form_11002
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11003 (u v w : ℝ) : ℝ :=
  (2764565809 / 32768 : ℝ)*u^3 + (306850449 / 8192 : ℝ)*u^2*v^1 + (8231609847 / 32768 : ℝ)*u^2*w^1 + (1892019231 / 32768 : ℝ)*u^1*v^2 + (1164311787 / 16384 : ℝ)*u^1*v^1*w^1 + (4081494309 / 16384 : ℝ)*u^1*w^2 + (93034575 / 8192 : ℝ)*v^3 + (1863021555 / 32768 : ℝ)*v^2*w^1 + (549166659 / 16384 : ℝ)*v^1*w^2 + (84246719 / 1024 : ℝ)*w^3

private theorem form_11003_pos : ConePositive form_11003 := by
  intro u v w hu hv hw hs
  unfold form_11003
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1100 (u v w : ℝ) : ℝ :=
  (194481 / 16 : ℝ)*u^3 + (2242485 / 64 : ℝ)*u^2*v^1 + (22097187 / 256 : ℝ)*u^2*w^1 + (8519175 / 256 : ℝ)*u^1*v^2 + (82779795 / 512 : ℝ)*u^1*v^1*w^1 + (-13232919 / 256 : ℝ)*u^1*w^2 + (10631331 / 1024 : ℝ)*v^3 + (303519591 / 4096 : ℝ)*v^2*w^1 + (-55775073 / 1024 : ℝ)*v^1*w^2 + (2572950385 / 4096 : ℝ)*w^3

private theorem form_1100_pos : ConePositive form_1100 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1100 (u+v/2+w/2) (v/2) (w/2)) = form_11000 := by
      funext u v w; dsimp [form_1100, form_11000]; ring
    rw [he]
    exact form_11000_pos
  · have he : (fun u v w : ℝ => form_1100 (u/2) (u/2+v+w/2) (w/2)) = form_11001 := by
      funext u v w; dsimp [form_1100, form_11001]; ring
    rw [he]
    exact form_11001_pos
  · have he : (fun u v w : ℝ => form_1100 (u/2) (v/2) (u/2+v/2+w)) = form_11002 := by
      funext u v w; dsimp [form_1100, form_11002]; ring
    rw [he]
    exact form_11002_pos
  · have he : (fun u v w : ℝ => form_1100 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_11003 := by
      funext u v w; dsimp [form_1100, form_11003]; ring
    rw [he]
    exact form_11003_pos

private def form_11010 (u v w : ℝ) : ℝ :=
  (10631331 / 1024 : ℝ)*u^3 + (61605279 / 2048 : ℝ)*u^2*v^1 + (422364735 / 8192 : ℝ)*u^2*w^1 + (118465497 / 4096 : ℝ)*u^1*v^2 + (806880465 / 8192 : ℝ)*u^1*v^1*w^1 + (27333465 / 1024 : ℝ)*u^1*w^2 + (75548133 / 8192 : ℝ)*v^3 + (1531231839 / 32768 : ℝ)*v^2*w^1 + (49115865 / 2048 : ℝ)*v^1*w^2 + (2613859477 / 32768 : ℝ)*w^3

private theorem form_11010_pos : ConePositive form_11010 := by
  intro u v w hu hv hw hs
  unfold form_11010
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11011 (u v w : ℝ) : ℝ :=
  (75548133 / 8192 : ℝ)*u^3 + (54089451 / 2048 : ℝ)*u^2*v^1 + (1490085459 / 32768 : ℝ)*u^2*w^1 + (12829671 / 512 : ℝ)*u^1*v^2 + (351092619 / 4096 : ℝ)*u^1*v^1*w^1 + (308804883 / 16384 : ℝ)*u^1*w^2 + (1007073 / 128 : ℝ)*v^3 + (81979731 / 2048 : ℝ)*v^2*w^1 + (64372731 / 4096 : ℝ)*v^1*w^2 + (314770223 / 4096 : ℝ)*w^3

private theorem form_11011_pos : ConePositive form_11011 := by
  intro u v w hu hv hw hs
  unfold form_11011
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11012 (u v w : ℝ) : ℝ :=
  (2613859477 / 32768 : ℝ)*u^3 + (7752761391 / 32768 : ℝ)*u^2*v^1 + (7404242991 / 16384 : ℝ)*u^2*w^1 + (3828556635 / 16384 : ℝ)*u^1*v^2 + (1838318739 / 2048 : ℝ)*u^1*v^1*w^1 + (3694636143 / 4096 : ℝ)*u^1*w^2 + (314770223 / 4096 : ℝ)*v^3 + (1824248607 / 4096 : ℝ)*v^2*w^1 + (1841855607 / 2048 : ℝ)*v^1*w^2 + (319545431 / 512 : ℝ)*w^3

private theorem form_11012_pos : ConePositive form_11012 := by
  intro u v w hu hv hw hs
  unfold form_11012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11013 (u v w : ℝ) : ℝ :=
  (2613859477 / 32768 : ℝ)*u^3 + (49115865 / 2048 : ℝ)*u^2*v^1 + (7752761391 / 32768 : ℝ)*u^2*w^1 + (1531231839 / 32768 : ℝ)*u^1*v^2 + (703324749 / 16384 : ℝ)*u^1*v^1*w^1 + (3828556635 / 16384 : ℝ)*u^1*w^2 + (75548133 / 8192 : ℝ)*v^3 + (1490085459 / 32768 : ℝ)*v^2*w^1 + (308804883 / 16384 : ℝ)*v^1*w^2 + (314770223 / 4096 : ℝ)*w^3

private theorem form_11013_pos : ConePositive form_11013 := by
  intro u v w hu hv hw hs
  unfold form_11013
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1101 (u v w : ℝ) : ℝ :=
  (10631331 / 1024 : ℝ)*u^3 + (14855643 / 512 : ℝ)*u^2*v^1 + (294788763 / 4096 : ℝ)*u^2*w^1 + (6787233 / 256 : ℝ)*u^1*v^2 + (132835293 / 1024 : ℝ)*u^1*v^1*w^1 + (-139909029 / 2048 : ℝ)*u^1*w^2 + (1007073 / 128 : ℝ)*v^3 + (57809979 / 1024 : ℝ)*v^2*w^1 + (-75416979 / 1024 : ℝ)*v^1*w^2 + (319545431 / 512 : ℝ)*w^3

private theorem form_1101_pos : ConePositive form_1101 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1101 (u+v/2+w/2) (v/2) (w/2)) = form_11010 := by
      funext u v w; dsimp [form_1101, form_11010]; ring
    rw [he]
    exact form_11010_pos
  · have he : (fun u v w : ℝ => form_1101 (u/2) (u/2+v+w/2) (w/2)) = form_11011 := by
      funext u v w; dsimp [form_1101, form_11011]; ring
    rw [he]
    exact form_11011_pos
  · have he : (fun u v w : ℝ => form_1101 (u/2) (v/2) (u/2+v/2+w)) = form_11012 := by
      funext u v w; dsimp [form_1101, form_11012]; ring
    rw [he]
    exact form_11012_pos
  · have he : (fun u v w : ℝ => form_1101 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_11013 := by
      funext u v w; dsimp [form_1101, form_11013]; ring
    rw [he]
    exact form_11013_pos

private def form_1102 (u v w : ℝ) : ℝ :=
  (2572950385 / 4096 : ℝ)*u^3 + (7707477567 / 4096 : ℝ)*u^2*v^1 + (7824714507 / 2048 : ℝ)*u^2*w^1 + (3845470101 / 2048 : ℝ)*u^1*v^2 + (7824558825 / 1024 : ℝ)*u^1*v^1*w^1 + (8018966607 / 1024 : ℝ)*u^1*w^2 + (319545431 / 512 : ℝ)*v^3 + (3909962151 / 1024 : ℝ)*v^2*w^1 + (8028568239 / 1024 : ℝ)*v^1*w^2 + (2760979093 / 512 : ℝ)*w^3

private theorem form_1102_pos : ConePositive form_1102 := by
  intro u v w hu hv hw hs
  unfold form_1102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11030 (u v w : ℝ) : ℝ :=
  (2572950385 / 4096 : ℝ)*u^3 + (7495750863 / 8192 : ℝ)*u^2*v^1 + (7713164361 / 4096 : ℝ)*u^2*w^1 + (3788085081 / 8192 : ℝ)*u^1*v^2 + (14952528549 / 8192 : ℝ)*u^1*v^1*w^1 + (30824746491 / 16384 : ℝ)*u^1*w^2 + (84246719 / 1024 : ℝ)*v^3 + (7538518365 / 16384 : ℝ)*v^2*w^1 + (29820428379 / 32768 : ℝ)*v^1*w^2 + (10263865801 / 16384 : ℝ)*w^3

private theorem form_11030_pos : ConePositive form_11030 := by
  intro u v w hu hv hw hs
  unfold form_11030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11031 (u v w : ℝ) : ℝ :=
  (84246719 / 1024 : ℝ)*u^3 + (255757431 / 8192 : ℝ)*u^2*v^1 + (4006190715 / 16384 : ℝ)*u^2*w^1 + (431095563 / 8192 : ℝ)*u^1*v^2 + (475184445 / 8192 : ℝ)*u^1*v^1*w^1 + (7930395471 / 32768 : ℝ)*u^1*w^2 + (10631331 / 1024 : ℝ)*v^3 + (422364735 / 8192 : ℝ)*v^2*w^1 + (27333465 / 1024 : ℝ)*v^1*w^2 + (2613859477 / 32768 : ℝ)*w^3

private theorem form_11031_pos : ConePositive form_11031 := by
  intro u v w hu hv hw hs
  unfold form_11031
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11032 (u v w : ℝ) : ℝ :=
  (10263865801 / 16384 : ℝ)*u^3 + (29754130203 / 32768 : ℝ)*u^2*v^1 + (30758448315 / 16384 : ℝ)*u^2*w^1 + (7448651511 / 16384 : ℝ)*u^1*v^2 + (14829512607 / 8192 : ℝ)*u^1*v^1*w^1 + (7680015273 / 4096 : ℝ)*u^1*w^2 + (2613859477 / 32768 : ℝ)*v^3 + (7404242991 / 16384 : ℝ)*v^2*w^1 + (3694636143 / 4096 : ℝ)*v^1*w^2 + (319545431 / 512 : ℝ)*w^3

private theorem form_11032_pos : ConePositive form_11032 := by
  intro u v w hu hv hw hs
  unfold form_11032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11033 (u v w : ℝ) : ℝ :=
  (10263865801 / 16384 : ℝ)*u^3 + (29820428379 / 32768 : ℝ)*u^2*v^1 + (29754130203 / 32768 : ℝ)*u^2*w^1 + (7538518365 / 16384 : ℝ)*u^1*v^2 + (14992408011 / 16384 : ℝ)*u^1*v^1*w^1 + (7448651511 / 16384 : ℝ)*u^1*w^2 + (84246719 / 1024 : ℝ)*v^3 + (4006190715 / 16384 : ℝ)*v^2*w^1 + (7930395471 / 32768 : ℝ)*v^1*w^2 + (2613859477 / 32768 : ℝ)*w^3

private theorem form_11033_pos : ConePositive form_11033 := by
  intro u v w hu hv hw hs
  unfold form_11033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1103 (u v w : ℝ) : ℝ :=
  (2572950385 / 4096 : ℝ)*u^3 + (-55775073 / 1024 : ℝ)*u^2*v^1 + (7707477567 / 4096 : ℝ)*u^2*w^1 + (303519591 / 4096 : ℝ)*u^1*v^2 + (-250699881 / 2048 : ℝ)*u^1*v^1*w^1 + (3845470101 / 2048 : ℝ)*u^1*w^2 + (10631331 / 1024 : ℝ)*v^3 + (294788763 / 4096 : ℝ)*v^2*w^1 + (-139909029 / 2048 : ℝ)*v^1*w^2 + (319545431 / 512 : ℝ)*w^3

private theorem form_1103_pos : ConePositive form_1103 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1103 (u+v/2+w/2) (v/2) (w/2)) = form_11030 := by
      funext u v w; dsimp [form_1103, form_11030]; ring
    rw [he]
    exact form_11030_pos
  · have he : (fun u v w : ℝ => form_1103 (u/2) (u/2+v+w/2) (w/2)) = form_11031 := by
      funext u v w; dsimp [form_1103, form_11031]; ring
    rw [he]
    exact form_11031_pos
  · have he : (fun u v w : ℝ => form_1103 (u/2) (v/2) (u/2+v/2+w)) = form_11032 := by
      funext u v w; dsimp [form_1103, form_11032]; ring
    rw [he]
    exact form_11032_pos
  · have he : (fun u v w : ℝ => form_1103 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_11033 := by
      funext u v w; dsimp [form_1103, form_11033]; ring
    rw [he]
    exact form_11033_pos

private def form_110 (u v w : ℝ) : ℝ :=
  (194481 / 16 : ℝ)*u^3 + (1075599 / 32 : ℝ)*u^2*v^1 + (17429643 / 128 : ℝ)*u^2*w^1 + (1883007 / 64 : ℝ)*u^1*v^2 + (29980629 / 128 : ℝ)*u^1*v^1*w^1 + (-16498167 / 32 : ℝ)*u^1*w^2 + (1007073 / 128 : ℝ)*v^3 + (45725103 / 512 : ℝ)*v^2*w^1 + (-15898065 / 32 : ℝ)*v^1*w^2 + (2760979093 / 512 : ℝ)*w^3

private theorem form_110_pos : ConePositive form_110 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_110 (u+v/2+w/2) (v/2) (w/2)) = form_1100 := by
      funext u v w; dsimp [form_110, form_1100]; ring
    rw [he]
    exact form_1100_pos
  · have he : (fun u v w : ℝ => form_110 (u/2) (u/2+v+w/2) (w/2)) = form_1101 := by
      funext u v w; dsimp [form_110, form_1101]; ring
    rw [he]
    exact form_1101_pos
  · have he : (fun u v w : ℝ => form_110 (u/2) (v/2) (u/2+v/2+w)) = form_1102 := by
      funext u v w; dsimp [form_110, form_1102]; ring
    rw [he]
    exact form_1102_pos
  · have he : (fun u v w : ℝ => form_110 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1103 := by
      funext u v w; dsimp [form_110, form_1103]; ring
    rw [he]
    exact form_1103_pos

private def form_11100 (u v w : ℝ) : ℝ :=
  (1007073 / 128 : ℝ)*u^3 + (11340081 / 512 : ℝ)*u^2*v^1 + (79000551 / 2048 : ℝ)*u^2*w^1 + (42172731 / 2048 : ℝ)*u^1*v^2 + (291994857 / 4096 : ℝ)*u^1*v^1*w^1 + (20391105 / 2048 : ℝ)*u^1*w^2 + (51689907 / 8192 : ℝ)*v^3 + (1064821527 / 32768 : ℝ)*v^2*w^1 + (52380363 / 8192 : ℝ)*v^1*w^2 + (2408504497 / 32768 : ℝ)*w^3

private theorem form_11100_pos : ConePositive form_11100 := by
  intro u v w hu hv hw hs
  unfold form_11100
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111010 (u v w : ℝ) : ℝ :=
  (51689907 / 8192 : ℝ)*u^3 + (296518239 / 16384 : ℝ)*u^2*v^1 + (1630615599 / 65536 : ℝ)*u^2*w^1 + (564923241 / 32768 : ℝ)*u^1*v^2 + (3100105161 / 65536 : ℝ)*u^1*v^1*w^1 + (165042165 / 8192 : ℝ)*u^1*w^2 + (357280389 / 65536 : ℝ)*v^3 + (5867197695 / 262144 : ℝ)*v^2*w^1 + (305152503 / 16384 : ℝ)*v^1*w^2 + (3501408853 / 262144 : ℝ)*w^3

private theorem form_111010_pos : ConePositive form_111010 := by
  intro u v w hu hv hw hs
  unfold form_111010
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111011 (u v w : ℝ) : ℝ :=
  (357280389 / 65536 : ℝ)*u^3 + (253458963 / 16384 : ℝ)*u^2*v^1 + (5635176435 / 262144 : ℝ)*u^2*w^1 + (59628231 / 4096 : ℝ)*u^1*v^2 + (1323762111 / 32768 : ℝ)*u^1*v^1*w^1 + (2104649715 / 131072 : ℝ)*u^1*w^2 + (4648185 / 1024 : ℝ)*v^3 + (309000699 / 16384 : ℝ)*v^2*w^1 + (473590047 / 32768 : ℝ)*v^1*w^2 + (386461187 / 32768 : ℝ)*w^3

private theorem form_111011_pos : ConePositive form_111011 := by
  intro u v w hu hv hw hs
  unfold form_111011
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111012 (u v w : ℝ) : ℝ :=
  (3501408853 / 262144 : ℝ)*u^3 + (10105317327 / 262144 : ℝ)*u^2*v^1 + (7863551919 / 131072 : ℝ)*u^2*w^1 + (4847823771 / 131072 : ℝ)*u^1*v^2 + (1906442181 / 16384 : ℝ)*u^1*v^1*w^1 + (3426746439 / 32768 : ℝ)*u^1*w^2 + (386461187 / 32768 : ℝ)*v^3 + (1845177075 / 32768 : ℝ)*v^2*w^1 + (1680587727 / 16384 : ℝ)*v^1*w^2 + (285573773 / 4096 : ℝ)*w^3

private theorem form_111012_pos : ConePositive form_111012 := by
  intro u v w hu hv hw hs
  unfold form_111012
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111013 (u v w : ℝ) : ℝ :=
  (3501408853 / 262144 : ℝ)*u^3 + (305152503 / 16384 : ℝ)*u^2*v^1 + (10105317327 / 262144 : ℝ)*u^2*w^1 + (5867197695 / 262144 : ℝ)*u^1*v^2 + (4549427421 / 131072 : ℝ)*u^1*v^1*w^1 + (4847823771 / 131072 : ℝ)*u^1*w^2 + (357280389 / 65536 : ℝ)*v^3 + (5635176435 / 262144 : ℝ)*v^2*w^1 + (2104649715 / 131072 : ℝ)*v^1*w^2 + (386461187 / 32768 : ℝ)*w^3

private theorem form_111013_pos : ConePositive form_111013 := by
  intro u v w hu hv hw hs
  unfold form_111013
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11101 (u v w : ℝ) : ℝ :=
  (51689907 / 8192 : ℝ)*u^3 + (70724259 / 4096 : ℝ)*u^2*v^1 + (1010336715 / 32768 : ℝ)*u^2*w^1 + (31739121 / 2048 : ℝ)*u^1*v^2 + (451847745 / 8192 : ℝ)*u^1*v^1*w^1 + (-138837 / 16384 : ℝ)*u^1*w^2 + (4648185 / 1024 : ℝ)*v^3 + (197444259 / 8192 : ℝ)*v^2*w^1 + (-32854911 / 8192 : ℝ)*v^1*w^2 + (285573773 / 4096 : ℝ)*w^3

private theorem form_11101_pos : ConePositive form_11101 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_11101 (u+v/2+w/2) (v/2) (w/2)) = form_111010 := by
      funext u v w; dsimp [form_11101, form_111010]; ring
    rw [he]
    exact form_111010_pos
  · have he : (fun u v w : ℝ => form_11101 (u/2) (u/2+v+w/2) (w/2)) = form_111011 := by
      funext u v w; dsimp [form_11101, form_111011]; ring
    rw [he]
    exact form_111011_pos
  · have he : (fun u v w : ℝ => form_11101 (u/2) (v/2) (u/2+v/2+w)) = form_111012 := by
      funext u v w; dsimp [form_11101, form_111012]; ring
    rw [he]
    exact form_111012_pos
  · have he : (fun u v w : ℝ => form_11101 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_111013 := by
      funext u v w; dsimp [form_11101, form_111013]; ring
    rw [he]
    exact form_111013_pos

private def form_11102 (u v w : ℝ) : ℝ :=
  (2408504497 / 32768 : ℝ)*u^3 + (7108777263 / 32768 : ℝ)*u^2*v^1 + (7062384651 / 16384 : ℝ)*u^2*w^1 + (3492456261 / 16384 : ℝ)*u^1*v^2 + (6993663117 / 8192 : ℝ)*u^1*v^1*w^1 + (7215258015 / 8192 : ℝ)*u^1*w^2 + (285573773 / 4096 : ℝ)*v^3 + (3459740187 / 8192 : ℝ)*v^2*w^1 + (7182634455 / 8192 : ℝ)*v^1*w^2 + (2529151525 / 4096 : ℝ)*w^3

private theorem form_11102_pos : ConePositive form_11102 := by
  intro u v w hu hv hw hs
  unfold form_11102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111030 (u v w : ℝ) : ℝ :=
  (2408504497 / 32768 : ℝ)*u^3 + (7435034943 / 65536 : ℝ)*u^2*v^1 + (7167145377 / 32768 : ℝ)*u^2*w^1 + (4354688961 / 65536 : ℝ)*u^1*v^2 + (14650175757 / 65536 : ℝ)*u^1*v^1*w^1 + (28427980539 / 131072 : ℝ)*u^1*w^2 + (60775111 / 4096 : ℝ)*v^3 + (8520609501 / 131072 : ℝ)*v^2*w^1 + (28849951419 / 262144 : ℝ)*v^1*w^2 + (9393392233 / 131072 : ℝ)*w^3

private theorem form_111030_pos : ConePositive form_111030 := by
  intro u v w hu hv hw hs
  unfold form_111030
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111031 (u v w : ℝ) : ℝ :=
  (60775111 / 4096 : ℝ)*u^3 + (1479721695 / 65536 : ℝ)*u^2*v^1 + (5645642235 / 131072 : ℝ)*u^2*w^1 + (1685100411 / 65536 : ℝ)*u^1*v^2 + (2801800677 / 65536 : ℝ)*u^1*v^1*w^1 + (10903135791 / 262144 : ℝ)*u^1*w^2 + (51689907 / 8192 : ℝ)*v^3 + (1630615599 / 65536 : ℝ)*v^2*w^1 + (165042165 / 8192 : ℝ)*v^1*w^2 + (3501408853 / 262144 : ℝ)*w^3

private theorem form_111031_pos : ConePositive form_111031 := by
  intro u v w hu hv hw hs
  unfold form_111031
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111032 (u v w : ℝ) : ℝ :=
  (9393392233 / 131072 : ℝ)*u^3 + (28354343739 / 262144 : ℝ)*u^2*v^1 + (27932372859 / 131072 : ℝ)*u^2*w^1 + (8063006535 / 131072 : ℝ)*u^1*v^2 + (13944768951 / 65536 : ℝ)*u^1*v^1*w^1 + (6919341537 / 32768 : ℝ)*u^1*w^2 + (3501408853 / 262144 : ℝ)*v^3 + (7863551919 / 131072 : ℝ)*v^2*w^1 + (3426746439 / 32768 : ℝ)*v^1*w^2 + (285573773 / 4096 : ℝ)*w^3

private theorem form_111032_pos : ConePositive form_111032 := by
  intro u v w hu hv hw hs
  unfold form_111032
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111033 (u v w : ℝ) : ℝ :=
  (9393392233 / 131072 : ℝ)*u^3 + (28849951419 / 262144 : ℝ)*u^2*v^1 + (28354343739 / 262144 : ℝ)*u^2*w^1 + (8520609501 / 131072 : ℝ)*u^1*v^2 + (16590818907 / 131072 : ℝ)*u^1*v^1*w^1 + (8063006535 / 131072 : ℝ)*u^1*w^2 + (60775111 / 4096 : ℝ)*v^3 + (5645642235 / 131072 : ℝ)*v^2*w^1 + (10903135791 / 262144 : ℝ)*v^1*w^2 + (3501408853 / 262144 : ℝ)*w^3

private theorem form_111033_pos : ConePositive form_111033 := by
  intro u v w hu hv hw hs
  unfold form_111033
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11103 (u v w : ℝ) : ℝ :=
  (2408504497 / 32768 : ℝ)*u^3 + (52380363 / 8192 : ℝ)*u^2*v^1 + (7108777263 / 32768 : ℝ)*u^2*w^1 + (1064821527 / 32768 : ℝ)*u^1*v^2 + (106363551 / 16384 : ℝ)*u^1*v^1*w^1 + (3492456261 / 16384 : ℝ)*u^1*w^2 + (51689907 / 8192 : ℝ)*v^3 + (1010336715 / 32768 : ℝ)*v^2*w^1 + (-138837 / 16384 : ℝ)*v^1*w^2 + (285573773 / 4096 : ℝ)*w^3

private theorem form_11103_pos : ConePositive form_11103 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_11103 (u+v/2+w/2) (v/2) (w/2)) = form_111030 := by
      funext u v w; dsimp [form_11103, form_111030]; ring
    rw [he]
    exact form_111030_pos
  · have he : (fun u v w : ℝ => form_11103 (u/2) (u/2+v+w/2) (w/2)) = form_111031 := by
      funext u v w; dsimp [form_11103, form_111031]; ring
    rw [he]
    exact form_111031_pos
  · have he : (fun u v w : ℝ => form_11103 (u/2) (v/2) (u/2+v/2+w)) = form_111032 := by
      funext u v w; dsimp [form_11103, form_111032]; ring
    rw [he]
    exact form_111032_pos
  · have he : (fun u v w : ℝ => form_11103 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_111033 := by
      funext u v w; dsimp [form_11103, form_111033]; ring
    rw [he]
    exact form_111033_pos

private def form_1110 (u v w : ℝ) : ℝ :=
  (1007073 / 128 : ℝ)*u^3 + (5297643 / 256 : ℝ)*u^2*v^1 + (54830799 / 1024 : ℝ)*u^2*w^1 + (8897283 / 512 : ℝ)*u^1*v^2 + (91612611 / 1024 : ℝ)*u^1*v^1*w^1 + (-23262285 / 256 : ℝ)*u^1*w^2 + (4648185 / 1024 : ℝ)*v^3 + (141666039 / 4096 : ℝ)*v^2*w^1 + (-50602515 / 512 : ℝ)*v^1*w^2 + (2529151525 / 4096 : ℝ)*w^3

private theorem form_1110_pos : ConePositive form_1110 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1110 (u+v/2+w/2) (v/2) (w/2)) = form_11100 := by
      funext u v w; dsimp [form_1110, form_11100]; ring
    rw [he]
    exact form_11100_pos
  · have he : (fun u v w : ℝ => form_1110 (u/2) (u/2+v+w/2) (w/2)) = form_11101 := by
      funext u v w; dsimp [form_1110, form_11101]; ring
    rw [he]
    exact form_11101_pos
  · have he : (fun u v w : ℝ => form_1110 (u/2) (v/2) (u/2+v/2+w)) = form_11102 := by
      funext u v w; dsimp [form_1110, form_11102]; ring
    rw [he]
    exact form_11102_pos
  · have he : (fun u v w : ℝ => form_1110 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_11103 := by
      funext u v w; dsimp [form_1110, form_11103]; ring
    rw [he]
    exact form_11103_pos

private def form_111100 (u v w : ℝ) : ℝ :=
  (4648185 / 1024 : ℝ)*u^3 + (51928209 / 4096 : ℝ)*u^2*v^1 + (293600655 / 16384 : ℝ)*u^2*w^1 + (191858787 / 16384 : ℝ)*u^1*v^2 + (1084827285 / 32768 : ℝ)*u^1*v^1*w^1 + (192461361 / 16384 : ℝ)*u^1*w^2 + (234055251 / 65536 : ℝ)*v^3 + (3969949815 / 262144 : ℝ)*v^2*w^1 + (659208867 / 65536 : ℝ)*v^1*w^2 + (2660151601 / 262144 : ℝ)*w^3

private theorem form_111100_pos : ConePositive form_111100 := by
  intro u v w hu hv hw hs
  unfold form_111100
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111101 (u v w : ℝ) : ℝ :=
  (234055251 / 65536 : ℝ)*u^3 + (318448179 / 32768 : ℝ)*u^2*v^1 + (3708872235 / 262144 : ℝ)*u^2*w^1 + (142443441 / 16384 : ℝ)*u^1*v^2 + (1666050057 / 65536 : ℝ)*u^1*v^1*w^1 + (945352011 / 131072 : ℝ)*u^1*w^2 + (20865033 / 8192 : ℝ)*v^3 + (736030323 / 65536 : ℝ)*v^2*w^1 + (356473257 / 65536 : ℝ)*v^1*w^2 + (275812217 / 32768 : ℝ)*w^3

private theorem form_111101_pos : ConePositive form_111101 := by
  intro u v w hu hv hw hs
  unfold form_111101
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111102 (u v w : ℝ) : ℝ :=
  (2660151601 / 262144 : ℝ)*u^3 + (7537908495 / 262144 : ℝ)*u^2*v^1 + (6440763915 / 131072 : ℝ)*u^2*w^1 + (3542152101 / 131072 : ℝ)*u^1*v^2 + (6177368277 / 65536 : ℝ)*u^1*v^1*w^1 + (6075475647 / 65536 : ℝ)*u^1*w^2 + (275812217 / 32768 : ℝ)*v^3 + (2953273347 / 65536 : ℝ)*v^2*w^1 + (5929630503 / 65536 : ℝ)*v^1*w^2 + (2146121413 / 32768 : ℝ)*w^3

private theorem form_111102_pos : ConePositive form_111102 := by
  intro u v w hu hv hw hs
  unfold form_111102
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111103 (u v w : ℝ) : ℝ :=
  (2660151601 / 262144 : ℝ)*u^3 + (659208867 / 65536 : ℝ)*u^2*v^1 + (7537908495 / 262144 : ℝ)*u^2*w^1 + (3969949815 / 262144 : ℝ)*u^1*v^2 + (2267476143 / 131072 : ℝ)*u^1*v^1*w^1 + (3542152101 / 131072 : ℝ)*u^1*w^2 + (234055251 / 65536 : ℝ)*v^3 + (3708872235 / 262144 : ℝ)*v^2*w^1 + (945352011 / 131072 : ℝ)*v^1*w^2 + (275812217 / 32768 : ℝ)*w^3

private theorem form_111103_pos : ConePositive form_111103 := by
  intro u v w hu hv hw hs
  unfold form_111103
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11110 (u v w : ℝ) : ℝ :=
  (4648185 / 1024 : ℝ)*u^3 + (24039099 / 2048 : ℝ)*u^2*v^1 + (182044215 / 8192 : ℝ)*u^2*w^1 + (39924171 / 4096 : ℝ)*u^1*v^2 + (305313183 / 8192 : ℝ)*u^1*v^1*w^1 + (-22680537 / 2048 : ℝ)*u^1*w^2 + (20865033 / 8192 : ℝ)*v^3 + (485649927 / 32768 : ℝ)*v^2*w^1 + (-63591717 / 4096 : ℝ)*v^1*w^2 + (2146121413 / 32768 : ℝ)*w^3

private theorem form_11110_pos : ConePositive form_11110 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_11110 (u+v/2+w/2) (v/2) (w/2)) = form_111100 := by
      funext u v w; dsimp [form_11110, form_111100]; ring
    rw [he]
    exact form_111100_pos
  · have he : (fun u v w : ℝ => form_11110 (u/2) (u/2+v+w/2) (w/2)) = form_111101 := by
      funext u v w; dsimp [form_11110, form_111101]; ring
    rw [he]
    exact form_111101_pos
  · have he : (fun u v w : ℝ => form_11110 (u/2) (v/2) (u/2+v/2+w)) = form_111102 := by
      funext u v w; dsimp [form_11110, form_111102]; ring
    rw [he]
    exact form_111102_pos
  · have he : (fun u v w : ℝ => form_11110 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_111103 := by
      funext u v w; dsimp [form_11110, form_111103]; ring
    rw [he]
    exact form_111103_pos

private def form_111110 (u v w : ℝ) : ℝ :=
  (20865033 / 8192 : ℝ)*u^3 + (107936955 / 16384 : ℝ)*u^2*v^1 + (667017351 / 65536 : ℝ)*u^2*w^1 + (180422235 / 32768 : ℝ)*u^1*v^2 + (1136264535 / 65536 : ℝ)*u^1*v^1*w^1 + (40148367 / 16384 : ℝ)*u^1*w^2 + (96004521 / 65536 : ℝ)*v^3 + (1865633319 / 262144 : ℝ)*v^2*w^1 + (19375095 / 32768 : ℝ)*v^1*w^2 + (1730430469 / 262144 : ℝ)*w^3

private theorem form_111110_pos : ConePositive form_111110 := by
  intro u v w hu hv hw hs
  unfold form_111110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1111110 (u v w : ℝ) : ℝ :=
  (96004521 / 65536 : ℝ)*u^3 + (503196219 / 131072 : ℝ)*u^2*v^1 + (2726363943 / 524288 : ℝ)*u^2*w^1 + (858803067 / 262144 : ℝ)*u^1*v^2 + (4746798279 / 524288 : ℝ)*u^1*v^1*w^1 + (454271583 / 131072 : ℝ)*u^1*w^2 + (472845033 / 524288 : ℝ)*v^3 + (8062522983 / 2097152 : ℝ)*v^2*w^1 + (704697135 / 262144 : ℝ)*v^1*w^2 + (2523479173 / 2097152 : ℝ)*w^3

private theorem form_1111110_pos : ConePositive form_1111110 := by
  intro u v w hu hv hw hs
  unfold form_1111110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1111111 (u v w : ℝ) : ℝ :=
  (472845033 / 524288 : ℝ)*u^3 + (8745813 / 4096 : ℝ)*u^2*v^1 + (6866238843 / 2097152 : ℝ)*u^2*w^1 + (199341 / 128 : ℝ)*u^1*v^2 + (84681189 / 16384 : ℝ)*u^1*v^1*w^1 + (1379930379 / 1048576 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (60327 / 32 : ℝ)*v^2*w^1 + (8519649 / 16384 : ℝ)*v^1*w^2 + (54590437 / 131072 : ℝ)*w^3

private theorem form_1111111_pos : ConePositive form_1111111 := by
  intro u v w hu hv hw hs
  unfold form_1111111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1111112 (u v w : ℝ) : ℝ :=
  (2523479173 / 2097152 : ℝ)*u^3 + (5939669271 / 2097152 : ℝ)*u^2*v^1 + (3936264855 / 1048576 : ℝ)*u^2*w^1 + (2144843331 / 1048576 : ℝ)*u^1*v^2 + (1505713107 / 262144 : ℝ)*u^1*v^1*w^1 + (1514228067 / 262144 : ℝ)*u^1*w^2 + (54590437 / 131072 : ℝ)*v^3 + (129692715 / 65536 : ℝ)*v^2*w^1 + (157388967 / 32768 : ℝ)*v^1*w^2 + (76978273 / 16384 : ℝ)*w^3

private theorem form_1111112_pos : ConePositive form_1111112 := by
  intro u v w hu hv hw hs
  unfold form_1111112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1111113 (u v w : ℝ) : ℝ :=
  (2523479173 / 2097152 : ℝ)*u^3 + (704697135 / 262144 : ℝ)*u^2*v^1 + (5939669271 / 2097152 : ℝ)*u^2*w^1 + (8062522983 / 2097152 : ℝ)*u^1*v^2 + (4206503505 / 1048576 : ℝ)*u^1*v^1*w^1 + (2144843331 / 1048576 : ℝ)*u^1*w^2 + (472845033 / 524288 : ℝ)*v^3 + (6866238843 / 2097152 : ℝ)*v^2*w^1 + (1379930379 / 1048576 : ℝ)*v^1*w^2 + (54590437 / 131072 : ℝ)*w^3

private theorem form_1111113_pos : ConePositive form_1111113 := by
  intro u v w hu hv hw hs
  unfold form_1111113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111111 (u v w : ℝ) : ℝ :=
  (96004521 / 65536 : ℝ)*u^3 + (3362229 / 1024 : ℝ)*u^2*v^1 + (1574309691 / 262144 : ℝ)*u^2*w^1 + (137133 / 64 : ℝ)*u^1*v^2 + (36240741 / 4096 : ℝ)*u^1*v^1*w^1 + (-333250485 / 131072 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (44775 / 16 : ℝ)*v^2*w^1 + (-18386463 / 4096 : ℝ)*v^1*w^2 + (76978273 / 16384 : ℝ)*w^3

private theorem form_111111_pos : ConePositive form_111111 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_111111 (u+v/2+w/2) (v/2) (w/2)) = form_1111110 := by
      funext u v w; dsimp [form_111111, form_1111110]; ring
    rw [he]
    exact form_1111110_pos
  · have he : (fun u v w : ℝ => form_111111 (u/2) (u/2+v+w/2) (w/2)) = form_1111111 := by
      funext u v w; dsimp [form_111111, form_1111111]; ring
    rw [he]
    exact form_1111111_pos
  · have he : (fun u v w : ℝ => form_111111 (u/2) (v/2) (u/2+v/2+w)) = form_1111112 := by
      funext u v w; dsimp [form_111111, form_1111112]; ring
    rw [he]
    exact form_1111112_pos
  · have he : (fun u v w : ℝ => form_111111 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1111113 := by
      funext u v w; dsimp [form_111111, form_1111113]; ring
    rw [he]
    exact form_1111113_pos

private def form_111112 (u v w : ℝ) : ℝ :=
  (1730430469 / 262144 : ℝ)*u^3 + (4703918295 / 262144 : ℝ)*u^2*v^1 + (4870104471 / 131072 : ℝ)*u^2*w^1 + (2102594883 / 131072 : ℝ)*u^1*v^2 + (2290250763 / 32768 : ℝ)*u^1*v^1*w^1 + (2607967443 / 32768 : ℝ)*u^1*w^2 + (76978273 / 16384 : ℝ)*v^3 + (267707745 / 8192 : ℝ)*v^2*w^1 + (315943071 / 4096 : ℝ)*v^1*w^2 + (124550047 / 2048 : ℝ)*w^3

private theorem form_111112_pos : ConePositive form_111112 := by
  intro u v w hu hv hw hs
  unfold form_111112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1111130 (u v w : ℝ) : ℝ :=
  (1730430469 / 262144 : ℝ)*u^3 + (5346292167 / 524288 : ℝ)*u^2*v^1 + (4947604851 / 262144 : ℝ)*u^2*w^1 + (3683463123 / 524288 : ℝ)*u^1*v^2 + (9798315471 / 524288 : ℝ)*u^1*v^1*w^1 + (18804317763 / 1048576 : ℝ)*u^1*w^2 + (516885329 / 262144 : ℝ)*v^3 + (6570682125 / 1048576 : ℝ)*v^2*w^1 + (17789027571 / 2097152 : ℝ)*v^1*w^2 + (5935595449 / 1048576 : ℝ)*w^3

private theorem form_1111130_pos : ConePositive form_1111130 := by
  intro u v w hu hv hw hs
  unfold form_1111130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1111131 (u v w : ℝ) : ℝ :=
  (516885329 / 262144 : ℝ)*u^3 + (2519160825 / 524288 : ℝ)*u^2*v^1 + (5406379827 / 1048576 : ℝ)*u^2*w^1 + (3017687571 / 524288 : ℝ)*u^1*v^2 + (4340102271 / 524288 : ℝ)*u^1*v^1*w^1 + (9201205767 / 2097152 : ℝ)*u^1*w^2 + (96004521 / 65536 : ℝ)*v^3 + (2726363943 / 524288 : ℝ)*v^2*w^1 + (454271583 / 131072 : ℝ)*v^1*w^2 + (2523479173 / 2097152 : ℝ)*w^3

private theorem form_1111131_pos : ConePositive form_1111131 := by
  intro u v w hu hv hw hs
  unfold form_1111131
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1111132 (u v w : ℝ) : ℝ :=
  (5935595449 / 1048576 : ℝ)*u^3 + (15793964739 / 2097152 : ℝ)*u^2*v^1 + (16809254931 / 1048576 : ℝ)*u^2*w^1 + (4751648979 / 1048576 : ℝ)*u^1*v^2 + (6981750909 / 524288 : ℝ)*u^1*v^1*w^1 + (3950073435 / 262144 : ℝ)*u^1*w^2 + (2523479173 / 2097152 : ℝ)*v^3 + (3936264855 / 1048576 : ℝ)*v^2*w^1 + (1514228067 / 262144 : ℝ)*v^1*w^2 + (76978273 / 16384 : ℝ)*w^3

private theorem form_1111132_pos : ConePositive form_1111132 := by
  intro u v w hu hv hw hs
  unfold form_1111132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1111133 (u v w : ℝ) : ℝ :=
  (5935595449 / 1048576 : ℝ)*u^3 + (17789027571 / 2097152 : ℝ)*u^2*v^1 + (15793964739 / 2097152 : ℝ)*u^2*w^1 + (6570682125 / 1048576 : ℝ)*u^1*v^2 + (11333760879 / 1048576 : ℝ)*u^1*v^1*w^1 + (4751648979 / 1048576 : ℝ)*u^1*w^2 + (516885329 / 262144 : ℝ)*v^3 + (5406379827 / 1048576 : ℝ)*v^2*w^1 + (9201205767 / 2097152 : ℝ)*v^1*w^2 + (2523479173 / 2097152 : ℝ)*w^3

private theorem form_1111133_pos : ConePositive form_1111133 := by
  intro u v w hu hv hw hs
  unfold form_1111133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111113 (u v w : ℝ) : ℝ :=
  (1730430469 / 262144 : ℝ)*u^3 + (19375095 / 32768 : ℝ)*u^2*v^1 + (4703918295 / 262144 : ℝ)*u^2*w^1 + (1865633319 / 262144 : ℝ)*u^1*v^2 + (-251894991 / 131072 : ℝ)*u^1*v^1*w^1 + (2102594883 / 131072 : ℝ)*u^1*w^2 + (96004521 / 65536 : ℝ)*v^3 + (1574309691 / 262144 : ℝ)*v^2*w^1 + (-333250485 / 131072 : ℝ)*v^1*w^2 + (76978273 / 16384 : ℝ)*w^3

private theorem form_111113_pos : ConePositive form_111113 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_111113 (u+v/2+w/2) (v/2) (w/2)) = form_1111130 := by
      funext u v w; dsimp [form_111113, form_1111130]; ring
    rw [he]
    exact form_1111130_pos
  · have he : (fun u v w : ℝ => form_111113 (u/2) (u/2+v+w/2) (w/2)) = form_1111131 := by
      funext u v w; dsimp [form_111113, form_1111131]; ring
    rw [he]
    exact form_1111131_pos
  · have he : (fun u v w : ℝ => form_111113 (u/2) (v/2) (u/2+v/2+w)) = form_1111132 := by
      funext u v w; dsimp [form_111113, form_1111132]; ring
    rw [he]
    exact form_1111132_pos
  · have he : (fun u v w : ℝ => form_111113 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1111133 := by
      funext u v w; dsimp [form_111113, form_1111133]; ring
    rw [he]
    exact form_1111133_pos

private def form_11111 (u v w : ℝ) : ℝ :=
  (20865033 / 8192 : ℝ)*u^3 + (1416933 / 256 : ℝ)*u^2*v^1 + (416636955 / 32768 : ℝ)*u^2*w^1 + (106029 / 32 : ℝ)*u^1*v^2 + (17992485 / 1024 : ℝ)*u^1*v^1*w^1 + (-381233685 / 16384 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (36999 / 8 : ℝ)*v^2*w^1 + (-28853535 / 1024 : ℝ)*v^1*w^2 + (124550047 / 2048 : ℝ)*w^3

private theorem form_11111_pos : ConePositive form_11111 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_11111 (u+v/2+w/2) (v/2) (w/2)) = form_111110 := by
      funext u v w; dsimp [form_11111, form_111110]; ring
    rw [he]
    exact form_111110_pos
  · have he : (fun u v w : ℝ => form_11111 (u/2) (u/2+v+w/2) (w/2)) = form_111111 := by
      funext u v w; dsimp [form_11111, form_111111]; ring
    rw [he]
    exact form_111111_pos
  · have he : (fun u v w : ℝ => form_11111 (u/2) (v/2) (u/2+v/2+w)) = form_111112 := by
      funext u v w; dsimp [form_11111, form_111112]; ring
    rw [he]
    exact form_111112_pos
  · have he : (fun u v w : ℝ => form_11111 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_111113 := by
      funext u v w; dsimp [form_11111, form_111113]; ring
    rw [he]
    exact form_111113_pos

private def form_11112 (u v w : ℝ) : ℝ :=
  (2146121413 / 32768 : ℝ)*u^3 + (6292519095 / 32768 : ℝ)*u^2*v^1 + (6619808535 / 16384 : ℝ)*u^2*w^1 + (3069624003 / 16384 : ℝ)*u^1*v^2 + (3266369319 / 4096 : ℝ)*u^1*v^1*w^1 + (3491648523 / 4096 : ℝ)*u^1*w^2 + (124550047 / 2048 : ℝ)*v^3 + (100625919 / 256 : ℝ)*v^2*w^1 + (433725147 / 512 : ℝ)*v^1*w^2 + (77844287 / 128 : ℝ)*w^3

private theorem form_11112_pos : ConePositive form_11112 := by
  intro u v w hu hv hw hs
  unfold form_11112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111130 (u v w : ℝ) : ℝ :=
  (2146121413 / 32768 : ℝ)*u^3 + (5929630503 / 65536 : ℝ)*u^2*v^1 + (6365441667 / 32768 : ℝ)*u^2*w^1 + (2953273347 / 65536 : ℝ)*u^1*v^2 + (11588439423 / 65536 : ℝ)*u^1*v^1*w^1 + (25162650435 / 131072 : ℝ)*u^1*w^2 + (275812217 / 32768 : ℝ)*v^3 + (5674141197 / 131072 : ℝ)*v^2*w^1 + (22624028979 / 262144 : ℝ)*v^1*w^2 + (8285344633 / 131072 : ℝ)*w^3

private theorem form_111130_pos : ConePositive form_111130 := by
  intro u v w hu hv hw hs
  unfold form_111130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111131 (u v w : ℝ) : ℝ :=
  (275812217 / 32768 : ℝ)*u^3 + (356473257 / 65536 : ℝ)*u^2*v^1 + (3077341107 / 131072 : ℝ)*u^2*w^1 + (736030323 / 65536 : ℝ)*u^1*v^2 + (518957103 / 65536 : ℝ)*u^1*v^1*w^1 + (5678664519 / 262144 : ℝ)*u^1*w^2 + (20865033 / 8192 : ℝ)*v^3 + (667017351 / 65536 : ℝ)*v^2*w^1 + (40148367 / 16384 : ℝ)*v^1*w^2 + (1730430469 / 262144 : ℝ)*w^3

private theorem form_111131_pos : ConePositive form_111131 := by
  intro u v w hu hv hw hs
  unfold form_111131
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111132 (u v w : ℝ) : ℝ :=
  (8285344633 / 131072 : ℝ)*u^3 + (22010795907 / 262144 : ℝ)*u^2*v^1 + (24549417363 / 131072 : ℝ)*u^2*w^1 + (5113791027 / 131072 : ℝ)*u^1*v^2 + (10721472717 / 65536 : ℝ)*u^1*v^1*w^1 + (6058825131 / 32768 : ℝ)*u^1*w^2 + (1730430469 / 262144 : ℝ)*v^3 + (4870104471 / 131072 : ℝ)*v^2*w^1 + (2607967443 / 32768 : ℝ)*v^1*w^2 + (124550047 / 2048 : ℝ)*w^3

private theorem form_111132_pos : ConePositive form_111132 := by
  intro u v w hu hv hw hs
  unfold form_111132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111133 (u v w : ℝ) : ℝ :=
  (8285344633 / 131072 : ℝ)*u^3 + (22624028979 / 262144 : ℝ)*u^2*v^1 + (22010795907 / 262144 : ℝ)*u^2*w^1 + (5674141197 / 131072 : ℝ)*u^1*v^2 + (10795432527 / 131072 : ℝ)*u^1*v^1*w^1 + (5113791027 / 131072 : ℝ)*u^1*w^2 + (275812217 / 32768 : ℝ)*v^3 + (3077341107 / 131072 : ℝ)*v^2*w^1 + (5678664519 / 262144 : ℝ)*v^1*w^2 + (1730430469 / 262144 : ℝ)*w^3

private theorem form_111133_pos : ConePositive form_111133 := by
  intro u v w hu hv hw hs
  unfold form_111133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11113 (u v w : ℝ) : ℝ :=
  (2146121413 / 32768 : ℝ)*u^3 + (-63591717 / 4096 : ℝ)*u^2*v^1 + (6292519095 / 32768 : ℝ)*u^2*w^1 + (485649927 / 32768 : ℝ)*u^1*v^2 + (-633710175 / 16384 : ℝ)*u^1*v^1*w^1 + (3069624003 / 16384 : ℝ)*u^1*w^2 + (20865033 / 8192 : ℝ)*v^3 + (416636955 / 32768 : ℝ)*v^2*w^1 + (-381233685 / 16384 : ℝ)*v^1*w^2 + (124550047 / 2048 : ℝ)*w^3

private theorem form_11113_pos : ConePositive form_11113 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_11113 (u+v/2+w/2) (v/2) (w/2)) = form_111130 := by
      funext u v w; dsimp [form_11113, form_111130]; ring
    rw [he]
    exact form_111130_pos
  · have he : (fun u v w : ℝ => form_11113 (u/2) (u/2+v+w/2) (w/2)) = form_111131 := by
      funext u v w; dsimp [form_11113, form_111131]; ring
    rw [he]
    exact form_111131_pos
  · have he : (fun u v w : ℝ => form_11113 (u/2) (v/2) (u/2+v/2+w)) = form_111132 := by
      funext u v w; dsimp [form_11113, form_111132]; ring
    rw [he]
    exact form_111132_pos
  · have he : (fun u v w : ℝ => form_11113 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_111133 := by
      funext u v w; dsimp [form_11113, form_111133]; ring
    rw [he]
    exact form_111133_pos

private def form_1111 (u v w : ℝ) : ℝ :=
  (4648185 / 1024 : ℝ)*u^3 + (630909 / 64 : ℝ)*u^2*v^1 + (126265995 / 4096 : ℝ)*u^2*w^1 + (90477 / 16 : ℝ)*u^1*v^2 + (10361349 / 256 : ℝ)*u^1*v^1*w^1 + (-244877253 / 2048 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (33111 / 4 : ℝ)*v^2*w^1 + (-33340575 / 256 : ℝ)*v^1*w^2 + (77844287 / 128 : ℝ)*w^3

private theorem form_1111_pos : ConePositive form_1111 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1111 (u+v/2+w/2) (v/2) (w/2)) = form_11110 := by
      funext u v w; dsimp [form_1111, form_11110]; ring
    rw [he]
    exact form_11110_pos
  · have he : (fun u v w : ℝ => form_1111 (u/2) (u/2+v+w/2) (w/2)) = form_11111 := by
      funext u v w; dsimp [form_1111, form_11111]; ring
    rw [he]
    exact form_11111_pos
  · have he : (fun u v w : ℝ => form_1111 (u/2) (v/2) (u/2+v/2+w)) = form_11112 := by
      funext u v w; dsimp [form_1111, form_11112]; ring
    rw [he]
    exact form_11112_pos
  · have he : (fun u v w : ℝ => form_1111 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_11113 := by
      funext u v w; dsimp [form_1111, form_11113]; ring
    rw [he]
    exact form_11113_pos

private def form_1112 (u v w : ℝ) : ℝ :=
  (2529151525 / 4096 : ℝ)*u^3 + (7554831015 / 4096 : ℝ)*u^2*v^1 + (7773552855 / 2048 : ℝ)*u^2*w^1 + (3758373123 / 2048 : ℝ)*u^1*v^2 + (3879489141 / 512 : ℝ)*u^1*v^1*w^1 + (4007240967 / 512 : ℝ)*u^1*w^2 + (77844287 / 128 : ℝ)*v^3 + (967472019 / 256 : ℝ)*v^2*w^1 + (500936073 / 64 : ℝ)*v^1*w^2 + (345756539 / 64 : ℝ)*w^3

private theorem form_1112_pos : ConePositive form_1112 := by
  intro u v w hu hv hw hs
  unfold form_1112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11130 (u v w : ℝ) : ℝ :=
  (2529151525 / 4096 : ℝ)*u^3 + (7182634455 / 8192 : ℝ)*u^2*v^1 + (7571142795 / 4096 : ℝ)*u^2*w^1 + (3459740187 / 8192 : ℝ)*u^1*v^2 + (14291086167 / 8192 : ℝ)*u^1*v^1*w^1 + (30213862851 / 16384 : ℝ)*u^1*w^2 + (285573773 / 4096 : ℝ)*v^3 + (6853909389 / 16384 : ℝ)*v^2*w^1 + (28426529619 / 32768 : ℝ)*v^1*w^2 + (10045872985 / 16384 : ℝ)*w^3

private theorem form_11130_pos : ConePositive form_11130 := by
  intro u v w hu hv hw hs
  unfold form_11130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111310 (u v w : ℝ) : ℝ :=
  (285573773 / 4096 : ℝ)*u^3 + (1680587727 / 16384 : ℝ)*u^2*v^1 + (6788199567 / 32768 : ℝ)*u^2*w^1 + (1845177075 / 32768 : ℝ)*u^1*v^2 + (824977587 / 4096 : ℝ)*u^1*v^1*w^1 + (26883237099 / 131072 : ℝ)*u^1*w^2 + (386461187 / 32768 : ℝ)*v^3 + (7170418773 / 131072 : ℝ)*v^2*w^1 + (25898252667 / 262144 : ℝ)*v^1*w^2 + (8868774781 / 131072 : ℝ)*w^3

private theorem form_111310_pos : ConePositive form_111310 := by
  intro u v w hu hv hw hs
  unfold form_111310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111311 (u v w : ℝ) : ℝ :=
  (386461187 / 32768 : ℝ)*u^3 + (473590047 / 32768 : ℝ)*u^2*v^1 + (4427244717 / 131072 : ℝ)*u^2*w^1 + (309000699 / 16384 : ℝ)*u^1*v^2 + (859420779 / 32768 : ℝ)*u^1*v^1*w^1 + (8423001111 / 262144 : ℝ)*u^1*w^2 + (4648185 / 1024 : ℝ)*v^3 + (293600655 / 16384 : ℝ)*v^2*w^1 + (192461361 / 16384 : ℝ)*v^1*w^2 + (2660151601 / 262144 : ℝ)*w^3

private theorem form_111311_pos : ConePositive form_111311 := by
  intro u v w hu hv hw hs
  unfold form_111311
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111312 (u v w : ℝ) : ℝ :=
  (8868774781 / 131072 : ℝ)*u^3 + (25344427155 / 262144 : ℝ)*u^2*v^1 + (26329411587 / 131072 : ℝ)*u^2*w^1 + (6662037069 / 131072 : ℝ)*u^1*v^2 + (3103586733 / 16384 : ℝ)*u^1*v^1*w^1 + (6511286811 / 32768 : ℝ)*u^1*w^2 + (2660151601 / 262144 : ℝ)*v^3 + (6440763915 / 131072 : ℝ)*v^2*w^1 + (6075475647 / 65536 : ℝ)*v^1*w^2 + (2146121413 / 32768 : ℝ)*w^3

private theorem form_111312_pos : ConePositive form_111312 := by
  intro u v w hu hv hw hs
  unfold form_111312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_111313 (u v w : ℝ) : ℝ :=
  (8868774781 / 131072 : ℝ)*u^3 + (25898252667 / 262144 : ℝ)*u^2*v^1 + (25344427155 / 262144 : ℝ)*u^2*w^1 + (7170418773 / 131072 : ℝ)*u^1*v^2 + (13839807429 / 131072 : ℝ)*u^1*v^1*w^1 + (6662037069 / 131072 : ℝ)*u^1*w^2 + (386461187 / 32768 : ℝ)*v^3 + (4427244717 / 131072 : ℝ)*v^2*w^1 + (8423001111 / 262144 : ℝ)*v^1*w^2 + (2660151601 / 262144 : ℝ)*w^3

private theorem form_111313_pos : ConePositive form_111313 := by
  intro u v w hu hv hw hs
  unfold form_111313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11131 (u v w : ℝ) : ℝ :=
  (285573773 / 4096 : ℝ)*u^3 + (-32854911 / 8192 : ℝ)*u^2*v^1 + (3361314291 / 16384 : ℝ)*u^2*w^1 + (197444259 / 8192 : ℝ)*u^1*v^2 + (-122669049 / 8192 : ℝ)*u^1*v^1*w^1 + (6584209383 / 32768 : ℝ)*u^1*w^2 + (4648185 / 1024 : ℝ)*v^3 + (182044215 / 8192 : ℝ)*v^2*w^1 + (-22680537 / 2048 : ℝ)*v^1*w^2 + (2146121413 / 32768 : ℝ)*w^3

private theorem form_11131_pos : ConePositive form_11131 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_11131 (u+v/2+w/2) (v/2) (w/2)) = form_111310 := by
      funext u v w; dsimp [form_11131, form_111310]; ring
    rw [he]
    exact form_111310_pos
  · have he : (fun u v w : ℝ => form_11131 (u/2) (u/2+v+w/2) (w/2)) = form_111311 := by
      funext u v w; dsimp [form_11131, form_111311]; ring
    rw [he]
    exact form_111311_pos
  · have he : (fun u v w : ℝ => form_11131 (u/2) (v/2) (u/2+v/2+w)) = form_111312 := by
      funext u v w; dsimp [form_11131, form_111312]; ring
    rw [he]
    exact form_111312_pos
  · have he : (fun u v w : ℝ => form_11131 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_111313 := by
      funext u v w; dsimp [form_11131, form_111313]; ring
    rw [he]
    exact form_111313_pos

private def form_11132 (u v w : ℝ) : ℝ :=
  (10045872985 / 16384 : ℝ)*u^3 + (28274041827 / 32768 : ℝ)*u^2*v^1 + (30061375059 / 16384 : ℝ)*u^2*w^1 + (6692731107 / 16384 : ℝ)*u^1*v^2 + (14053663989 / 8192 : ℝ)*u^1*v^1*w^1 + (7494898899 / 4096 : ℝ)*u^1*w^2 + (2146121413 / 32768 : ℝ)*v^3 + (6619808535 / 16384 : ℝ)*v^2*w^1 + (3491648523 / 4096 : ℝ)*v^1*w^2 + (77844287 / 128 : ℝ)*w^3

private theorem form_11132_pos : ConePositive form_11132 := by
  intro u v w hu hv hw hs
  unfold form_11132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11133 (u v w : ℝ) : ℝ :=
  (10045872985 / 16384 : ℝ)*u^3 + (28426529619 / 32768 : ℝ)*u^2*v^1 + (28274041827 / 32768 : ℝ)*u^2*w^1 + (6853909389 / 16384 : ℝ)*u^1*v^2 + (13552176063 / 16384 : ℝ)*u^1*v^1*w^1 + (6692731107 / 16384 : ℝ)*u^1*w^2 + (285573773 / 4096 : ℝ)*v^3 + (3361314291 / 16384 : ℝ)*v^2*w^1 + (6584209383 / 32768 : ℝ)*v^1*w^2 + (2146121413 / 32768 : ℝ)*w^3

private theorem form_11133_pos : ConePositive form_11133 := by
  intro u v w hu hv hw hs
  unfold form_11133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1113 (u v w : ℝ) : ℝ :=
  (2529151525 / 4096 : ℝ)*u^3 + (-50602515 / 512 : ℝ)*u^2*v^1 + (7554831015 / 4096 : ℝ)*u^2*w^1 + (141666039 / 4096 : ℝ)*u^1*v^2 + (-446379303 / 2048 : ℝ)*u^1*v^1*w^1 + (3758373123 / 2048 : ℝ)*u^1*w^2 + (4648185 / 1024 : ℝ)*v^3 + (126265995 / 4096 : ℝ)*v^2*w^1 + (-244877253 / 2048 : ℝ)*v^1*w^2 + (77844287 / 128 : ℝ)*w^3

private theorem form_1113_pos : ConePositive form_1113 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1113 (u+v/2+w/2) (v/2) (w/2)) = form_11130 := by
      funext u v w; dsimp [form_1113, form_11130]; ring
    rw [he]
    exact form_11130_pos
  · have he : (fun u v w : ℝ => form_1113 (u/2) (u/2+v+w/2) (w/2)) = form_11131 := by
      funext u v w; dsimp [form_1113, form_11131]; ring
    rw [he]
    exact form_11131_pos
  · have he : (fun u v w : ℝ => form_1113 (u/2) (v/2) (u/2+v/2+w)) = form_11132 := by
      funext u v w; dsimp [form_1113, form_11132]; ring
    rw [he]
    exact form_11132_pos
  · have he : (fun u v w : ℝ => form_1113 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_11133 := by
      funext u v w; dsimp [form_1113, form_11133]; ring
    rw [he]
    exact form_11133_pos

private def form_111 (u v w : ℝ) : ℝ :=
  (1007073 / 128 : ℝ)*u^3 + (284553 / 16 : ℝ)*u^2*v^1 + (42745923 / 512 : ℝ)*u^2*w^1 + (82701 / 8 : ℝ)*u^1*v^2 + (6919029 / 64 : ℝ)*u^1*v^1*w^1 + (-141837501 / 256 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (31167 / 2 : ℝ)*v^2*w^1 + (-35397471 / 64 : ℝ)*v^1*w^2 + (345756539 / 64 : ℝ)*w^3

private theorem form_111_pos : ConePositive form_111 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_111 (u+v/2+w/2) (v/2) (w/2)) = form_1110 := by
      funext u v w; dsimp [form_111, form_1110]; ring
    rw [he]
    exact form_1110_pos
  · have he : (fun u v w : ℝ => form_111 (u/2) (u/2+v+w/2) (w/2)) = form_1111 := by
      funext u v w; dsimp [form_111, form_1111]; ring
    rw [he]
    exact form_1111_pos
  · have he : (fun u v w : ℝ => form_111 (u/2) (v/2) (u/2+v/2+w)) = form_1112 := by
      funext u v w; dsimp [form_111, form_1112]; ring
    rw [he]
    exact form_1112_pos
  · have he : (fun u v w : ℝ => form_111 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1113 := by
      funext u v w; dsimp [form_111, form_1113]; ring
    rw [he]
    exact form_1113_pos

private def form_112 (u v w : ℝ) : ℝ :=
  (2760979093 / 512 : ℝ)*u^3 + (8292538911 / 512 : ℝ)*u^2*v^1 + (8414922615 / 256 : ℝ)*u^2*w^1 + (4148830851 / 256 : ℝ)*u^1*v^2 + (1053675363 / 16 : ℝ)*u^1*v^1*w^1 + (4282168797 / 64 : ℝ)*u^1*w^2 + (345756539 / 64 : ℝ)*v^3 + (2109936705 / 64 : ℝ)*v^2*w^1 + (134114553 / 2 : ℝ)*v^1*w^2 + (727404037 / 16 : ℝ)*w^3

private theorem form_112_pos : ConePositive form_112 := by
  intro u v w hu hv hw hs
  unfold form_112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1130 (u v w : ℝ) : ℝ :=
  (2760979093 / 512 : ℝ)*u^3 + (8028568239 / 1024 : ℝ)*u^2*v^1 + (8287738095 / 512 : ℝ)*u^2*w^1 + (3909962151 / 1024 : ℝ)*u^1*v^2 + (16052501955 / 1024 : ℝ)*u^1*v^1*w^1 + (33165676803 / 2048 : ℝ)*u^1*w^2 + (319545431 / 512 : ℝ)*v^3 + (7808999373 / 2048 : ℝ)*v^2*w^1 + (32090422371 / 4096 : ℝ)*v^1*w^2 + (11058616009 / 2048 : ℝ)*w^3

private theorem form_1130_pos : ConePositive form_1130 := by
  intro u v w hu hv hw hs
  unfold form_1130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11310 (u v w : ℝ) : ℝ :=
  (319545431 / 512 : ℝ)*u^3 + (1841855607 / 2048 : ℝ)*u^2*v^1 + (7658165415 / 4096 : ℝ)*u^2*w^1 + (1824248607 / 4096 : ℝ)*u^1*v^2 + (1834820541 / 1024 : ℝ)*u^1*v^1*w^1 + (30583649451 / 16384 : ℝ)*u^1*w^2 + (314770223 / 4096 : ℝ)*v^3 + (7245680469 / 16384 : ℝ)*v^2*w^1 + (29237587803 / 32768 : ℝ)*v^1*w^2 + (10176416797 / 16384 : ℝ)*w^3

private theorem form_11310_pos : ConePositive form_11310 := by
  intro u v w hu hv hw hs
  unfold form_11310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11311 (u v w : ℝ) : ℝ :=
  (314770223 / 4096 : ℝ)*u^3 + (64372731 / 4096 : ℝ)*u^2*v^1 + (3725928717 / 16384 : ℝ)*u^2*w^1 + (81979731 / 2048 : ℝ)*u^1*v^2 + (105571767 / 4096 : ℝ)*u^1*v^1*w^1 + (7342249719 / 32768 : ℝ)*u^1*w^2 + (1007073 / 128 : ℝ)*v^3 + (79000551 / 2048 : ℝ)*v^2*w^1 + (20391105 / 2048 : ℝ)*v^1*w^2 + (2408504497 / 32768 : ℝ)*w^3

private theorem form_11311_pos : ConePositive form_11311 := by
  intro u v w hu hv hw hs
  unfold form_11311
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11312 (u v w : ℝ) : ℝ :=
  (10176416797 / 16384 : ℝ)*u^3 + (29128789683 / 32768 : ℝ)*u^2*v^1 + (30474851331 / 16384 : ℝ)*u^2*w^1 + (7120752765 / 16384 : ℝ)*u^1*v^2 + (3624809391 / 2048 : ℝ)*u^1*v^1*w^1 + (7603766355 / 4096 : ℝ)*u^1*w^2 + (2408504497 / 32768 : ℝ)*v^3 + (7062384651 / 16384 : ℝ)*v^2*w^1 + (7215258015 / 8192 : ℝ)*v^1*w^2 + (2529151525 / 4096 : ℝ)*w^3

private theorem form_11312_pos : ConePositive form_11312 := by
  intro u v w hu hv hw hs
  unfold form_11312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_11313 (u v w : ℝ) : ℝ :=
  (10176416797 / 16384 : ℝ)*u^3 + (29237587803 / 32768 : ℝ)*u^2*v^1 + (29128789683 / 32768 : ℝ)*u^2*w^1 + (7245680469 / 16384 : ℝ)*u^1*v^2 + (14371820085 / 16384 : ℝ)*u^1*v^1*w^1 + (7120752765 / 16384 : ℝ)*u^1*w^2 + (314770223 / 4096 : ℝ)*v^3 + (3725928717 / 16384 : ℝ)*v^2*w^1 + (7342249719 / 32768 : ℝ)*v^1*w^2 + (2408504497 / 32768 : ℝ)*w^3

private theorem form_11313_pos : ConePositive form_11313 := by
  intro u v w hu hv hw hs
  unfold form_11313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1131 (u v w : ℝ) : ℝ :=
  (319545431 / 512 : ℝ)*u^3 + (-75416979 / 1024 : ℝ)*u^2*v^1 + (3823620243 / 2048 : ℝ)*u^2*w^1 + (57809979 / 1024 : ℝ)*u^1*v^2 + (-168049293 / 1024 : ℝ)*u^1*v^1*w^1 + (7620078135 / 4096 : ℝ)*u^1*w^2 + (1007073 / 128 : ℝ)*v^3 + (54830799 / 1024 : ℝ)*v^2*w^1 + (-23262285 / 256 : ℝ)*v^1*w^2 + (2529151525 / 4096 : ℝ)*w^3

private theorem form_1131_pos : ConePositive form_1131 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1131 (u+v/2+w/2) (v/2) (w/2)) = form_11310 := by
      funext u v w; dsimp [form_1131, form_11310]; ring
    rw [he]
    exact form_11310_pos
  · have he : (fun u v w : ℝ => form_1131 (u/2) (u/2+v+w/2) (w/2)) = form_11311 := by
      funext u v w; dsimp [form_1131, form_11311]; ring
    rw [he]
    exact form_11311_pos
  · have he : (fun u v w : ℝ => form_1131 (u/2) (v/2) (u/2+v/2+w)) = form_11312 := by
      funext u v w; dsimp [form_1131, form_11312]; ring
    rw [he]
    exact form_11312_pos
  · have he : (fun u v w : ℝ => form_1131 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_11313 := by
      funext u v w; dsimp [form_1131, form_11313]; ring
    rw [he]
    exact form_11313_pos

private def form_1132 (u v w : ℝ) : ℝ :=
  (11058616009 / 2048 : ℝ)*u^3 + (32110764819 / 4096 : ℝ)*u^2*v^1 + (33186019251 / 2048 : ℝ)*u^2*w^1 + (7789864635 / 2048 : ℝ)*u^1*v^2 + (16043538441 / 1024 : ℝ)*u^1*v^1*w^1 + (8297909319 / 512 : ℝ)*u^1*w^2 + (2529151525 / 4096 : ℝ)*v^3 + (7773552855 / 2048 : ℝ)*v^2*w^1 + (4007240967 / 512 : ℝ)*v^1*w^2 + (345756539 / 64 : ℝ)*w^3

private theorem form_1132_pos : ConePositive form_1132 := by
  intro u v w hu hv hw hs
  unfold form_1132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1133 (u v w : ℝ) : ℝ :=
  (11058616009 / 2048 : ℝ)*u^3 + (32090422371 / 4096 : ℝ)*u^2*v^1 + (32110764819 / 4096 : ℝ)*u^2*w^1 + (7808999373 / 2048 : ℝ)*u^1*v^2 + (15603417207 / 2048 : ℝ)*u^1*v^1*w^1 + (7789864635 / 2048 : ℝ)*u^1*w^2 + (319545431 / 512 : ℝ)*v^3 + (3823620243 / 2048 : ℝ)*v^2*w^1 + (7620078135 / 4096 : ℝ)*v^1*w^2 + (2529151525 / 4096 : ℝ)*w^3

private theorem form_1133_pos : ConePositive form_1133 := by
  intro u v w hu hv hw hs
  unfold form_1133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_113 (u v w : ℝ) : ℝ :=
  (2760979093 / 512 : ℝ)*u^3 + (-15898065 / 32 : ℝ)*u^2*v^1 + (8292538911 / 512 : ℝ)*u^2*w^1 + (45725103 / 512 : ℝ)*u^1*v^2 + (-268605195 / 256 : ℝ)*u^1*v^1*w^1 + (4148830851 / 256 : ℝ)*u^1*w^2 + (1007073 / 128 : ℝ)*v^3 + (42745923 / 512 : ℝ)*v^2*w^1 + (-141837501 / 256 : ℝ)*v^1*w^2 + (345756539 / 64 : ℝ)*w^3

private theorem form_113_pos : ConePositive form_113 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_113 (u+v/2+w/2) (v/2) (w/2)) = form_1130 := by
      funext u v w; dsimp [form_113, form_1130]; ring
    rw [he]
    exact form_1130_pos
  · have he : (fun u v w : ℝ => form_113 (u/2) (u/2+v+w/2) (w/2)) = form_1131 := by
      funext u v w; dsimp [form_113, form_1131]; ring
    rw [he]
    exact form_1131_pos
  · have he : (fun u v w : ℝ => form_113 (u/2) (v/2) (u/2+v/2+w)) = form_1132 := by
      funext u v w; dsimp [form_113, form_1132]; ring
    rw [he]
    exact form_1132_pos
  · have he : (fun u v w : ℝ => form_113 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1133 := by
      funext u v w; dsimp [form_113, form_1133]; ring
    rw [he]
    exact form_1133_pos

private def form_11 (u v w : ℝ) : ℝ :=
  (194481 / 16 : ℝ)*u^3 + (123039 / 4 : ℝ)*u^2*v^1 + (15095871 / 64 : ℝ)*u^2*w^1 + (78813 / 4 : ℝ)*u^1*v^2 + (5291181 / 16 : ℝ)*u^1*v^1*w^1 + (-82255425 / 32 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (30195 / 1 : ℝ)*v^2*w^1 + (-36379263 / 16 : ℝ)*v^1*w^2 + (727404037 / 16 : ℝ)*w^3

private theorem form_11_pos : ConePositive form_11 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_11 (u+v/2+w/2) (v/2) (w/2)) = form_110 := by
      funext u v w; dsimp [form_11, form_110]; ring
    rw [he]
    exact form_110_pos
  · have he : (fun u v w : ℝ => form_11 (u/2) (u/2+v+w/2) (w/2)) = form_111 := by
      funext u v w; dsimp [form_11, form_111]; ring
    rw [he]
    exact form_111_pos
  · have he : (fun u v w : ℝ => form_11 (u/2) (v/2) (u/2+v/2+w)) = form_112 := by
      funext u v w; dsimp [form_11, form_112]; ring
    rw [he]
    exact form_112_pos
  · have he : (fun u v w : ℝ => form_11 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_113 := by
      funext u v w; dsimp [form_11, form_113]; ring
    rw [he]
    exact form_113_pos

private def form_12 (u v w : ℝ) : ℝ :=
  (2886535549 / 64 : ℝ)*u^3 + (8686724475 / 64 : ℝ)*u^2*v^1 + (8751078711 / 32 : ℝ)*u^2*w^1 + (4354927323 / 32 : ℝ)*u^1*v^2 + (8778288231 / 16 : ℝ)*u^1*v^1*w^1 + (2211876159 / 4 : ℝ)*u^1*w^2 + (727404037 / 16 : ℝ)*v^3 + (4400803485 / 16 : ℝ)*v^2*w^1 + (1109356077 / 2 : ℝ)*v^1*w^2 + (1491427601 / 4 : ℝ)*w^3

private theorem form_12_pos : ConePositive form_12 := by
  intro u v w hu hv hw hs
  unfold form_12
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_130 (u v w : ℝ) : ℝ :=
  (2886535549 / 64 : ℝ)*u^3 + (8503780347 / 128 : ℝ)*u^2*v^1 + (8673165561 / 64 : ℝ)*u^2*w^1 + (4181707533 / 128 : ℝ)*u^1*v^2 + (17030507481 / 128 : ℝ)*u^1*v^1*w^1 + (34742910243 / 256 : ℝ)*u^1*w^2 + (85842131 / 16 : ℝ)*v^3 + (8372620365 / 256 : ℝ)*v^2*w^1 + (34102578411 / 512 : ℝ)*v^1*w^2 + (11596365409 / 256 : ℝ)*w^3

private theorem form_130_pos : ConePositive form_130 := by
  intro u v w hu hv hw hs
  unfold form_130
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1310 (u v w : ℝ) : ℝ :=
  (85842131 / 16 : ℝ)*u^3 + (1998925899 / 256 : ℝ)*u^2*v^1 + (8250049875 / 512 : ℝ)*u^2*w^1 + (1955435445 / 512 : ℝ)*u^1*v^2 + (4000186353 / 256 : ℝ)*u^1*v^1*w^1 + (33032690571 / 2048 : ℝ)*u^1*w^2 + (322401221 / 512 : ℝ)*v^3 + (7821144405 / 2048 : ℝ)*v^2*w^1 + (32015152203 / 4096 : ℝ)*v^1*w^2 + (11020259053 / 2048 : ℝ)*w^3

private theorem form_1310_pos : ConePositive form_1310 := by
  intro u v w hu hv hw hs
  unfold form_1310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_13110 (u v w : ℝ) : ℝ :=
  (322401221 / 512 : ℝ)*u^3 + (118271943 / 128 : ℝ)*u^2*v^1 + (7737031929 / 4096 : ℝ)*u^2*w^1 + (970072095 / 2048 : ℝ)*u^1*v^2 + (7558274007 / 4096 : ℝ)*u^1*v^1*w^1 + (30940723155 / 16384 : ℝ)*u^1*w^2 + (88130291 / 1024 : ℝ)*v^3 + (7735992261 / 16384 : ℝ)*v^2*w^1 + (30182189715 / 32768 : ℝ)*v^1*w^2 + (10309409725 / 16384 : ℝ)*w^3

private theorem form_13110_pos : ConePositive form_13110 := by
  intro u v w hu hv hw hs
  unfold form_13110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_13111 (u v w : ℝ) : ℝ :=
  (88130291 / 1024 : ℝ)*u^3 + (87491397 / 2048 : ℝ)*u^2*v^1 + (4205669469 / 16384 : ℝ)*u^2*w^1 + (31797423 / 512 : ℝ)*u^1*v^2 + (168255717 / 2048 : ℝ)*u^1*v^1*w^1 + (8355785007 / 32768 : ℝ)*u^1*w^2 + (194481 / 16 : ℝ)*v^3 + (31432275 / 512 : ℝ)*v^2*w^1 + (40296543 / 1024 : ℝ)*v^1*w^2 + (2764565809 / 32768 : ℝ)*w^3

private theorem form_13111_pos : ConePositive form_13111 := by
  intro u v w hu hv hw hs
  unfold form_13111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_13112 (u v w : ℝ) : ℝ :=
  (10309409725 / 16384 : ℝ)*u^3 + (30157201755 / 32768 : ℝ)*u^2*v^1 + (30915735195 / 16384 : ℝ)*u^2*w^1 + (7679996529 / 16384 : ℝ)*u^1*v^2 + (7524029151 / 4096 : ℝ)*u^1*v^1*w^1 + (7724537949 / 4096 : ℝ)*u^1*w^2 + (2764565809 / 32768 : ℝ)*v^3 + (7648952739 / 16384 : ℝ)*v^2*w^1 + (7507124451 / 8192 : ℝ)*v^1*w^2 + (2572950385 / 4096 : ℝ)*w^3

private theorem form_13112_pos : ConePositive form_13112 := by
  intro u v w hu hv hw hs
  unfold form_13112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_13113 (u v w : ℝ) : ℝ :=
  (10309409725 / 16384 : ℝ)*u^3 + (30182189715 / 32768 : ℝ)*u^2*v^1 + (30157201755 / 32768 : ℝ)*u^2*w^1 + (7735992261 / 16384 : ℝ)*u^1*v^2 + (15421078209 / 16384 : ℝ)*u^1*v^1*w^1 + (7679996529 / 16384 : ℝ)*u^1*w^2 + (88130291 / 1024 : ℝ)*v^3 + (4205669469 / 16384 : ℝ)*v^2*w^1 + (8355785007 / 32768 : ℝ)*v^1*w^2 + (2764565809 / 32768 : ℝ)*w^3

private theorem form_13113_pos : ConePositive form_13113 := by
  intro u v w hu hv hw hs
  unfold form_13113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1311 (u v w : ℝ) : ℝ :=
  (322401221 / 512 : ℝ)*u^3 + (-21028119 / 512 : ℝ)*u^2*v^1 + (3868217277 / 2048 : ℝ)*u^2*w^1 + (22462335 / 256 : ℝ)*u^1*v^2 + (-47322723 / 512 : ℝ)*u^1*v^1*w^1 + (7730224743 / 4096 : ℝ)*u^1*w^2 + (194481 / 16 : ℝ)*v^3 + (22097187 / 256 : ℝ)*v^2*w^1 + (-13232919 / 256 : ℝ)*v^1*w^2 + (2572950385 / 4096 : ℝ)*w^3

private theorem form_1311_pos : ConePositive form_1311 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1311 (u+v/2+w/2) (v/2) (w/2)) = form_13110 := by
      funext u v w; dsimp [form_1311, form_13110]; ring
    rw [he]
    exact form_13110_pos
  · have he : (fun u v w : ℝ => form_1311 (u/2) (u/2+v+w/2) (w/2)) = form_13111 := by
      funext u v w; dsimp [form_1311, form_13111]; ring
    rw [he]
    exact form_13111_pos
  · have he : (fun u v w : ℝ => form_1311 (u/2) (v/2) (u/2+v/2+w)) = form_13112 := by
      funext u v w; dsimp [form_1311, form_13112]; ring
    rw [he]
    exact form_13112_pos
  · have he : (fun u v w : ℝ => form_1311 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_13113 := by
      funext u v w; dsimp [form_1311, form_13113]; ring
    rw [he]
    exact form_13113_pos

private def form_1312 (u v w : ℝ) : ℝ :=
  (11020259053 / 2048 : ℝ)*u^3 + (32071325379 / 4096 : ℝ)*u^2*v^1 + (33088863747 / 2048 : ℝ)*u^2*w^1 + (7830401301 / 2048 : ℝ)*u^1*v^2 + (250595139 / 16 : ℝ)*u^1*v^1*w^1 + (8278136463 / 512 : ℝ)*u^1*w^2 + (2572950385 / 4096 : ℝ)*v^3 + (7824714507 / 2048 : ℝ)*v^2*w^1 + (8018966607 / 1024 : ℝ)*v^1*w^2 + (2760979093 / 512 : ℝ)*w^3

private theorem form_1312_pos : ConePositive form_1312 := by
  intro u v w hu hv hw hs
  unfold form_1312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_1313 (u v w : ℝ) : ℝ :=
  (11020259053 / 2048 : ℝ)*u^3 + (32015152203 / 4096 : ℝ)*u^2*v^1 + (32071325379 / 4096 : ℝ)*u^2*w^1 + (7821144405 / 2048 : ℝ)*u^1*v^2 + (15655950189 / 2048 : ℝ)*u^1*v^1*w^1 + (7830401301 / 2048 : ℝ)*u^1*w^2 + (322401221 / 512 : ℝ)*v^3 + (3868217277 / 2048 : ℝ)*v^2*w^1 + (7730224743 / 4096 : ℝ)*v^1*w^2 + (2572950385 / 4096 : ℝ)*w^3

private theorem form_1313_pos : ConePositive form_1313 := by
  intro u v w hu hv hw hs
  unfold form_1313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_131 (u v w : ℝ) : ℝ :=
  (85842131 / 16 : ℝ)*u^3 + (-61285245 / 128 : ℝ)*u^2*v^1 + (4129627587 / 256 : ℝ)*u^2*w^1 + (17794791 / 128 : ℝ)*u^1*v^2 + (-127106679 / 128 : ℝ)*u^1*v^1*w^1 + (8273335647 / 512 : ℝ)*u^1*w^2 + (194481 / 16 : ℝ)*v^3 + (17429643 / 128 : ℝ)*v^2*w^1 + (-16498167 / 32 : ℝ)*v^1*w^2 + (2760979093 / 512 : ℝ)*w^3

private theorem form_131_pos : ConePositive form_131 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_131 (u+v/2+w/2) (v/2) (w/2)) = form_1310 := by
      funext u v w; dsimp [form_131, form_1310]; ring
    rw [he]
    exact form_1310_pos
  · have he : (fun u v w : ℝ => form_131 (u/2) (u/2+v+w/2) (w/2)) = form_1311 := by
      funext u v w; dsimp [form_131, form_1311]; ring
    rw [he]
    exact form_1311_pos
  · have he : (fun u v w : ℝ => form_131 (u/2) (v/2) (u/2+v/2+w)) = form_1312 := by
      funext u v w; dsimp [form_131, form_1312]; ring
    rw [he]
    exact form_1312_pos
  · have he : (fun u v w : ℝ => form_131 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_1313 := by
      funext u v w; dsimp [form_131, form_1313]; ring
    rw [he]
    exact form_1313_pos

private def form_132 (u v w : ℝ) : ℝ :=
  (11596365409 / 256 : ℝ)*u^3 + (34194950379 / 512 : ℝ)*u^2*v^1 + (34835282211 / 256 : ℝ)*u^2*w^1 + (8410121799 / 256 : ℝ)*u^1*v^2 + (17114194899 / 128 : ℝ)*u^1*v^1*w^1 + (8719351545 / 64 : ℝ)*u^1*w^2 + (2760979093 / 512 : ℝ)*v^3 + (8414922615 / 256 : ℝ)*v^2*w^1 + (4282168797 / 64 : ℝ)*v^1*w^2 + (727404037 / 16 : ℝ)*w^3

private theorem form_132_pos : ConePositive form_132 := by
  intro u v w hu hv hw hs
  unfold form_132
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_133 (u v w : ℝ) : ℝ :=
  (11596365409 / 256 : ℝ)*u^3 + (34102578411 / 512 : ℝ)*u^2*v^1 + (34194950379 / 512 : ℝ)*u^2*w^1 + (8372620365 / 256 : ℝ)*u^1*v^2 + (16786804179 / 256 : ℝ)*u^1*v^1*w^1 + (8410121799 / 256 : ℝ)*u^1*w^2 + (85842131 / 16 : ℝ)*v^3 + (4129627587 / 256 : ℝ)*v^2*w^1 + (8273335647 / 512 : ℝ)*v^1*w^2 + (2760979093 / 512 : ℝ)*w^3

private theorem form_133_pos : ConePositive form_133 := by
  intro u v w hu hv hw hs
  unfold form_133
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_13 (u v w : ℝ) : ℝ :=
  (2886535549 / 64 : ℝ)*u^3 + (-38956575 / 16 : ℝ)*u^2*v^1 + (8686724475 / 64 : ℝ)*u^2*w^1 + (15461019 / 64 : ℝ)*u^1*v^2 + (-159997341 / 32 : ℝ)*u^1*v^1*w^1 + (4354927323 / 32 : ℝ)*u^1*w^2 + (194481 / 16 : ℝ)*v^3 + (15095871 / 64 : ℝ)*v^2*w^1 + (-82255425 / 32 : ℝ)*v^1*w^2 + (727404037 / 16 : ℝ)*w^3

private theorem form_13_pos : ConePositive form_13 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_13 (u+v/2+w/2) (v/2) (w/2)) = form_130 := by
      funext u v w; dsimp [form_13, form_130]; ring
    rw [he]
    exact form_130_pos
  · have he : (fun u v w : ℝ => form_13 (u/2) (u/2+v+w/2) (w/2)) = form_131 := by
      funext u v w; dsimp [form_13, form_131]; ring
    rw [he]
    exact form_131_pos
  · have he : (fun u v w : ℝ => form_13 (u/2) (v/2) (u/2+v/2+w)) = form_132 := by
      funext u v w; dsimp [form_13, form_132]; ring
    rw [he]
    exact form_132_pos
  · have he : (fun u v w : ℝ => form_13 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_133 := by
      funext u v w; dsimp [form_13, form_133]; ring
    rw [he]
    exact form_133_pos

private def form_1 (u v w : ℝ) : ℝ :=
  (13284 / 1 : ℝ)*u^3 + (45198 / 1 : ℝ)*u^2*v^1 + (4635045 / 8 : ℝ)*u^2*w^1 + (76869 / 2 : ℝ)*u^1*v^2 + (4500585 / 4 : ℝ)*u^1*v^1*w^1 + (-50530485 / 4 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (59418 / 1 : ℝ)*v^2*w^1 + (-36858495 / 4 : ℝ)*v^1*w^2 + (1491427601 / 4 : ℝ)*w^3

private theorem form_1_pos : ConePositive form_1 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_1 (u+v/2+w/2) (v/2) (w/2)) = form_10 := by
      funext u v w; dsimp [form_1, form_10]; ring
    rw [he]
    exact form_10_pos
  · have he : (fun u v w : ℝ => form_1 (u/2) (u/2+v+w/2) (w/2)) = form_11 := by
      funext u v w; dsimp [form_1, form_11]; ring
    rw [he]
    exact form_11_pos
  · have he : (fun u v w : ℝ => form_1 (u/2) (v/2) (u/2+v/2+w)) = form_12 := by
      funext u v w; dsimp [form_1, form_12]; ring
    rw [he]
    exact form_12_pos
  · have he : (fun u v w : ℝ => form_1 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_13 := by
      funext u v w; dsimp [form_1, form_13]; ring
    rw [he]
    exact form_13_pos

private def form_2 (u v w : ℝ) : ℝ :=
  (2951670013 / 8 : ℝ)*u^3 + (8889986865 / 8 : ℝ)*u^2*v^1 + (8922942915 / 4 : ℝ)*u^2*w^1 + (4460610813 / 4 : ℝ)*u^1*v^2 + (17912135001 / 4 : ℝ)*u^1*v^1*w^1 + (4495553568 / 1 : ℝ)*u^1*w^2 + (1491427601 / 4 : ℝ)*v^3 + (8985424101 / 4 : ℝ)*v^2*w^1 + (4511200716 / 1 : ℝ)*v^1*w^2 + (3019832209 / 1 : ℝ)*w^3

private theorem form_2_pos : ConePositive form_2 := by
  intro u v w hu hv hw hs
  unfold form_2
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_30 (u v w : ℝ) : ℝ :=
  (2951670013 / 8 : ℝ)*u^3 + (8754121113 / 16 : ℝ)*u^2*v^1 + (2218124613 / 2 : ℝ)*u^2*w^1 + (541114029 / 2 : ℝ)*u^1*v^2 + (4385795367 / 4 : ℝ)*u^1*v^1*w^1 + (35556205395 / 32 : ℝ)*u^1*w^2 + (713869909 / 16 : ℝ)*v^3 + (8675296677 / 32 : ℝ)*v^2*w^1 + (35152402479 / 64 : ℝ)*v^1*w^2 + (11872866853 / 32 : ℝ)*w^3

private theorem form_30_pos : ConePositive form_30 := by
  intro u v w hu hv hw hs
  unfold form_30
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_310 (u v w : ℝ) : ℝ :=
  (713869909 / 16 : ℝ)*u^3 + (2095916949 / 32 : ℝ)*u^2*v^1 + (8583911121 / 64 : ℝ)*u^2*w^1 + (64222977 / 2 : ℝ)*u^1*v^2 + (8401145193 / 64 : ℝ)*u^1*v^1*w^1 + (34401694395 / 256 : ℝ)*u^1*w^2 + (21040649 / 4 : ℝ)*v^3 + (8238109173 / 256 : ℝ)*v^2*w^1 + (33670457667 / 512 : ℝ)*v^1*w^2 + (11487943669 / 256 : ℝ)*w^3

private theorem form_310_pos : ConePositive form_310 := by
  intro u v w hu hv hw hs
  unfold form_310
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_3110 (u v w : ℝ) : ℝ :=
  (21040649 / 4 : ℝ)*u^3 + (60919887 / 8 : ℝ)*u^2*v^1 + (8097177333 / 512 : ℝ)*u^2*w^1 + (475291341 / 128 : ℝ)*u^1*v^2 + (7815495093 / 512 : ℝ)*u^1*v^1*w^1 + (32454949107 / 2048 : ℝ)*u^1*w^2 + (156682525 / 256 : ℝ)*v^3 + (7622934597 / 2048 : ℝ)*v^2*w^1 + (31328558403 / 4096 : ℝ)*v^1*w^2 + (10839027277 / 2048 : ℝ)*w^3

private theorem form_3110_pos : ConePositive form_3110 := by
  intro u v w hu hv hw hs
  unfold form_3110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_31110 (u v w : ℝ) : ℝ :=
  (156682525 / 256 : ℝ)*u^3 + (459560043 / 512 : ℝ)*u^2*v^1 + (7539034341 / 4096 : ℝ)*u^2*w^1 + (476368467 / 1024 : ℝ)*u^1*v^2 + (7372280997 / 4096 : ℝ)*u^1*v^1*w^1 + (30224809731 / 16384 : ℝ)*u^1*w^2 + (176891653 / 2048 : ℝ)*v^3 + (7643631525 / 16384 : ℝ)*v^2*w^1 + (29561210019 / 32768 : ℝ)*v^1*w^2 + (10096329181 / 16384 : ℝ)*w^3

private theorem form_31110_pos : ConePositive form_31110 := by
  intro u v w hu hv hw hs
  unfold form_31110
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_31111 (u v w : ℝ) : ℝ :=
  (176891653 / 2048 : ℝ)*u^3 + (13576623 / 256 : ℝ)*u^2*v^1 + (4267135725 / 16384 : ℝ)*u^2*w^1 + (9374517 / 128 : ℝ)*u^1*v^2 + (13652115 / 128 : ℝ)*u^1*v^1*w^1 + (8572548351 / 32768 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (9417285 / 128 : ℝ)*v^2*w^1 + (27430995 / 512 : ℝ)*v^1*w^2 + (2868493777 / 32768 : ℝ)*w^3

private theorem form_31111_pos : ConePositive form_31111 := by
  intro u v w hu hv hw hs
  unfold form_31111
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_31112 (u v w : ℝ) : ℝ :=
  (10096329181 / 16384 : ℝ)*u^3 + (29689565643 / 32768 : ℝ)*u^2*v^1 + (30353165355 / 16384 : ℝ)*u^2*w^1 + (7711223001 / 16384 : ℝ)*u^1*v^2 + (7438165641 / 4096 : ℝ)*u^1*v^1*w^1 + (7603212153 / 4096 : ℝ)*u^1*w^2 + (2868493777 / 32768 : ℝ)*v^3 + (7727689491 / 16384 : ℝ)*v^2*w^1 + (7452603891 / 8192 : ℝ)*v^1*w^2 + (2538996913 / 4096 : ℝ)*w^3

private theorem form_31112_pos : ConePositive form_31112 := by
  intro u v w hu hv hw hs
  unfold form_31112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_31113 (u v w : ℝ) : ℝ :=
  (10096329181 / 16384 : ℝ)*u^3 + (29561210019 / 32768 : ℝ)*u^2*v^1 + (29689565643 / 32768 : ℝ)*u^2*w^1 + (7643631525 / 16384 : ℝ)*u^1*v^2 + (15359349081 / 16384 : ℝ)*u^1*v^1*w^1 + (7711223001 / 16384 : ℝ)*u^1*w^2 + (176891653 / 2048 : ℝ)*v^3 + (4267135725 / 16384 : ℝ)*v^2*w^1 + (8572548351 / 32768 : ℝ)*v^1*w^2 + (2868493777 / 32768 : ℝ)*w^3

private theorem form_31113_pos : ConePositive form_31113 := by
  intro u v w hu hv hw hs
  unfold form_31113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_3111 (u v w : ℝ) : ℝ :=
  (156682525 / 256 : ℝ)*u^3 + (-2621883 / 64 : ℝ)*u^2*v^1 + (3778653741 / 2048 : ℝ)*u^2*w^1 + (6823989 / 64 : ℝ)*u^1*v^2 + (-2589159 / 32 : ℝ)*u^1*v^1*w^1 + (7589433567 / 4096 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (6866757 / 64 : ℝ)*v^2*w^1 + (-5137089 / 128 : ℝ)*v^1*w^2 + (2538996913 / 4096 : ℝ)*w^3

private theorem form_3111_pos : ConePositive form_3111 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_3111 (u+v/2+w/2) (v/2) (w/2)) = form_31110 := by
      funext u v w; dsimp [form_3111, form_31110]; ring
    rw [he]
    exact form_31110_pos
  · have he : (fun u v w : ℝ => form_3111 (u/2) (u/2+v+w/2) (w/2)) = form_31111 := by
      funext u v w; dsimp [form_3111, form_31111]; ring
    rw [he]
    exact form_31111_pos
  · have he : (fun u v w : ℝ => form_3111 (u/2) (v/2) (u/2+v/2+w)) = form_31112 := by
      funext u v w; dsimp [form_3111, form_31112]; ring
    rw [he]
    exact form_31112_pos
  · have he : (fun u v w : ℝ => form_3111 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_31113 := by
      funext u v w; dsimp [form_3111, form_31113]; ring
    rw [he]
    exact form_31113_pos

private def form_3112 (u v w : ℝ) : ℝ :=
  (10839027277 / 2048 : ℝ)*u^3 + (31452823851 / 4096 : ℝ)*u^2*v^1 + (32579214555 / 2048 : ℝ)*u^2*w^1 + (7685405577 / 2048 : ℝ)*u^1*v^2 + (7877796945 / 512 : ℝ)*u^1*v^1*w^1 + (8159310057 / 512 : ℝ)*u^1*w^2 + (2538996913 / 4096 : ℝ)*v^3 + (7699184163 / 2048 : ℝ)*v^2*w^1 + (7891245699 / 1024 : ℝ)*v^1*w^2 + (2724257041 / 512 : ℝ)*w^3

private theorem form_3112_pos : ConePositive form_3112 := by
  intro u v w hu hv hw hs
  unfold form_3112
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_3113 (u v w : ℝ) : ℝ :=
  (10839027277 / 2048 : ℝ)*u^3 + (31328558403 / 4096 : ℝ)*u^2*v^1 + (31452823851 / 4096 : ℝ)*u^2*w^1 + (7622934597 / 2048 : ℝ)*u^1*v^2 + (15312447225 / 2048 : ℝ)*u^1*v^1*w^1 + (7685405577 / 2048 : ℝ)*u^1*w^2 + (156682525 / 256 : ℝ)*v^3 + (3778653741 / 2048 : ℝ)*v^2*w^1 + (7589433567 / 4096 : ℝ)*v^1*w^2 + (2538996913 / 4096 : ℝ)*w^3

private theorem form_3113_pos : ConePositive form_3113 := by
  intro u v w hu hv hw hs
  unfold form_3113
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_311 (u v w : ℝ) : ℝ :=
  (21040649 / 4 : ℝ)*u^3 + (-550515 / 1 : ℝ)*u^2*v^1 + (4057372725 / 256 : ℝ)*u^2*w^1 + (5548725 / 32 : ℝ)*u^1*v^2 + (-2199225 / 2 : ℝ)*u^1*v^1*w^1 + (8145848991 / 512 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (5591493 / 32 : ℝ)*v^2*w^1 + (-17595339 / 32 : ℝ)*v^1*w^2 + (2724257041 / 512 : ℝ)*w^3

private theorem form_311_pos : ConePositive form_311 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_311 (u+v/2+w/2) (v/2) (w/2)) = form_3110 := by
      funext u v w; dsimp [form_311, form_3110]; ring
    rw [he]
    exact form_3110_pos
  · have he : (fun u v w : ℝ => form_311 (u/2) (u/2+v+w/2) (w/2)) = form_3111 := by
      funext u v w; dsimp [form_311, form_3111]; ring
    rw [he]
    exact form_3111_pos
  · have he : (fun u v w : ℝ => form_311 (u/2) (v/2) (u/2+v/2+w)) = form_3112 := by
      funext u v w; dsimp [form_311, form_3112]; ring
    rw [he]
    exact form_3112_pos
  · have he : (fun u v w : ℝ => form_311 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_3113 := by
      funext u v w; dsimp [form_311, form_3113]; ring
    rw [he]
    exact form_3113_pos

private def form_312 (u v w : ℝ) : ℝ :=
  (11487943669 / 256 : ℝ)*u^3 + (33794730891 / 512 : ℝ)*u^2*v^1 + (34525967619 / 256 : ℝ)*u^2*w^1 + (8300072769 / 256 : ℝ)*u^1*v^2 + (8463195297 / 64 : ℝ)*u^1*v^1*w^1 + (8646047733 / 64 : ℝ)*u^1*w^2 + (2724257041 / 512 : ℝ)*v^3 + (8313533835 / 256 : ℝ)*v^2*w^1 + (8476662519 / 128 : ℝ)*v^1*w^2 + (2886535549 / 64 : ℝ)*w^3

private theorem form_312_pos : ConePositive form_312 := by
  intro u v w hu hv hw hs
  unfold form_312
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_313 (u v w : ℝ) : ℝ :=
  (11487943669 / 256 : ℝ)*u^3 + (33670457667 / 512 : ℝ)*u^2*v^1 + (33794730891 / 512 : ℝ)*u^2*w^1 + (8238109173 / 256 : ℝ)*u^1*v^2 + (16542095241 / 256 : ℝ)*u^1*v^1*w^1 + (8300072769 / 256 : ℝ)*u^1*w^2 + (21040649 / 4 : ℝ)*v^3 + (4057372725 / 256 : ℝ)*v^2*w^1 + (8145848991 / 512 : ℝ)*v^1*w^2 + (2724257041 / 512 : ℝ)*w^3

private theorem form_313_pos : ConePositive form_313 := by
  intro u v w hu hv hw hs
  unfold form_313
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_31 (u v w : ℝ) : ℝ :=
  (713869909 / 16 : ℝ)*u^3 + (-22846389 / 8 : ℝ)*u^2*v^1 + (4300691667 / 32 : ℝ)*u^2*w^1 + (4911093 / 16 : ℝ)*u^1*v^2 + (-22845093 / 4 : ℝ)*u^1*v^1*w^1 + (8632488819 / 64 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (4953861 / 16 : ℝ)*v^2*w^1 + (-2858502 / 1 : ℝ)*v^1*w^2 + (2886535549 / 64 : ℝ)*w^3

private theorem form_31_pos : ConePositive form_31 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_31 (u+v/2+w/2) (v/2) (w/2)) = form_310 := by
      funext u v w; dsimp [form_31, form_310]; ring
    rw [he]
    exact form_310_pos
  · have he : (fun u v w : ℝ => form_31 (u/2) (u/2+v+w/2) (w/2)) = form_311 := by
      funext u v w; dsimp [form_31, form_311]; ring
    rw [he]
    exact form_311_pos
  · have he : (fun u v w : ℝ => form_31 (u/2) (v/2) (u/2+v/2+w)) = form_312 := by
      funext u v w; dsimp [form_31, form_312]; ring
    rw [he]
    exact form_312_pos
  · have he : (fun u v w : ℝ => form_31 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_313 := by
      funext u v w; dsimp [form_31, form_313]; ring
    rw [he]
    exact form_313_pos

private def form_32 (u v w : ℝ) : ℝ :=
  (11872866853 / 32 : ℝ)*u^3 + (35277192807 / 64 : ℝ)*u^2*v^1 + (35680995723 / 32 : ℝ)*u^2*w^1 + (8737519797 / 32 : ℝ)*u^1*v^2 + (2208474969 / 2 : ℝ)*u^1*v^1*w^1 + (1116861702 / 1 : ℝ)*u^1*w^2 + (2886535549 / 64 : ℝ)*v^3 + (8751078711 / 32 : ℝ)*v^2*w^1 + (2211876159 / 4 : ℝ)*v^1*w^2 + (1491427601 / 4 : ℝ)*w^3

private theorem form_32_pos : ConePositive form_32 := by
  intro u v w hu hv hw hs
  unfold form_32
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_33 (u v w : ℝ) : ℝ :=
  (11872866853 / 32 : ℝ)*u^3 + (35152402479 / 64 : ℝ)*u^2*v^1 + (35277192807 / 64 : ℝ)*u^2*w^1 + (8675296677 / 32 : ℝ)*u^1*v^2 + (17416632897 / 32 : ℝ)*u^1*v^1*w^1 + (8737519797 / 32 : ℝ)*u^1*w^2 + (713869909 / 16 : ℝ)*v^3 + (4300691667 / 32 : ℝ)*v^2*w^1 + (8632488819 / 64 : ℝ)*v^1*w^2 + (2886535549 / 64 : ℝ)*w^3

private theorem form_33_pos : ConePositive form_33 := by
  intro u v w hu hv hw hs
  unfold form_33
  rcases positive_coordinate hs with hp | hp | hp <;> positivity

private def form_3 (u v w : ℝ) : ℝ :=
  (2951670013 / 8 : ℝ)*u^3 + (-50444463 / 4 : ℝ)*u^2*v^1 + (8889986865 / 8 : ℝ)*u^2*w^1 + (4592277 / 8 : ℝ)*u^1*v^2 + (-50463255 / 2 : ℝ)*u^1*v^1*w^1 + (4460610813 / 4 : ℝ)*u^1*w^2 + (13284 / 1 : ℝ)*v^3 + (4635045 / 8 : ℝ)*v^2*w^1 + (-50530485 / 4 : ℝ)*v^1*w^2 + (1491427601 / 4 : ℝ)*w^3

private theorem form_3_pos : ConePositive form_3 := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_3 (u+v/2+w/2) (v/2) (w/2)) = form_30 := by
      funext u v w; dsimp [form_3, form_30]; ring
    rw [he]
    exact form_30_pos
  · have he : (fun u v w : ℝ => form_3 (u/2) (u/2+v+w/2) (w/2)) = form_31 := by
      funext u v w; dsimp [form_3, form_31]; ring
    rw [he]
    exact form_31_pos
  · have he : (fun u v w : ℝ => form_3 (u/2) (v/2) (u/2+v/2+w)) = form_32 := by
      funext u v w; dsimp [form_3, form_32]; ring
    rw [he]
    exact form_32_pos
  · have he : (fun u v w : ℝ => form_3 (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_33 := by
      funext u v w; dsimp [form_3, form_33]; ring
    rw [he]
    exact form_33_pos

private def form_root (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (28026 / 1 : ℝ)*u^2*v^1 + (225270 / 1 : ℝ)*u^2*w^1 + (75897 / 1 : ℝ)*u^1*v^2 + (4111119 / 1 : ℝ)*u^1*v^1*w^1 + (-68389491 / 1 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (117864 / 1 : ℝ)*v^2*w^1 + (-37095195 / 1 : ℝ)*v^1*w^2 + (3019832209 / 1 : ℝ)*w^3

private theorem form_root_pos : ConePositive form_root := by
  apply cone_subdivision
  · have he : (fun u v w : ℝ => form_root (u+v/2+w/2) (v/2) (w/2)) = form_0 := by
      funext u v w; dsimp [form_root, form_0]; ring
    rw [he]
    exact form_0_pos
  · have he : (fun u v w : ℝ => form_root (u/2) (u/2+v+w/2) (w/2)) = form_1 := by
      funext u v w; dsimp [form_root, form_1]; ring
    rw [he]
    exact form_1_pos
  · have he : (fun u v w : ℝ => form_root (u/2) (v/2) (u/2+v/2+w)) = form_2 := by
      funext u v w; dsimp [form_root, form_2]; ring
    rw [he]
    exact form_2_pos
  · have he : (fun u v w : ℝ => form_root (u/2+v/2) (v/2+w/2) (u/2+w/2)) = form_3 := by
      funext u v w; dsimp [form_root, form_3]; ring
    rw [he]
    exact form_3_pos

def determinantForm (u v w : ℝ) : ℝ :=
  (2025 / 1 : ℝ)*u^3 + (28026 / 1 : ℝ)*u^2*v^1 + (225270 / 1 : ℝ)*u^2*w^1 + (75897 / 1 : ℝ)*u^1*v^2 + (4111119 / 1 : ℝ)*u^1*v^1*w^1 + (-68389491 / 1 : ℝ)*u^1*w^2 + (324 / 1 : ℝ)*v^3 + (117864 / 1 : ℝ)*v^2*w^1 + (-37095195 / 1 : ℝ)*v^1*w^2 + (3019832209 / 1 : ℝ)*w^3
theorem determinantForm_positive : ConePositive determinantForm := form_root_pos

end
end SPR.Polytope.QuarticTriangle
