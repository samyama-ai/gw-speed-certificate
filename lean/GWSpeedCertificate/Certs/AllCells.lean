import GWSpeedCertificate.Certs.Batch01
import GWSpeedCertificate.Certs.Batch02
import GWSpeedCertificate.Certs.Batch03
import GWSpeedCertificate.Certs.Batch04
import GWSpeedCertificate.Certs.Batch05
import GWSpeedCertificate.Certs.Batch06
import GWSpeedCertificate.Certs.Batch07
import GWSpeedCertificate.Certs.Batch08
import GWSpeedCertificate.Certs.Batch09
import GWSpeedCertificate.Certs.Batch10
import GWSpeedCertificate.Certs.Batch11
import GWSpeedCertificate.Certs.Batch12
import GWSpeedCertificate.Certs.Batch13
import GWSpeedCertificate.Certs.Batch14

/-!
# Contiguous Gluing of Certified Cells on `[117/100, 351/200]` (`AllCells.lean`)
-/

namespace GWSpeedCertificate.Certs

open MeasureTheory

theorem r_div_lam_strictAntiOn_117_to_1755 {mu : Measure InfTree23} [IsGWTree23 mu] :
    StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (351 / 200 : ℝ)) := by
  have h_0 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (6 / 5 : ℝ)) := by
    simpa only [show ((117 : ℝ) / (100 : ℝ)) = (117 / 100 : ℝ) by norm_num, show ((120 : ℝ) / (100 : ℝ)) = (6 / 5 : ℝ) by norm_num] using cell_00_anti (mu := mu)
  have hc_1 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (6 / 5 : ℝ) (123 / 100 : ℝ)) := by
    simpa only [show ((120 : ℝ) / (100 : ℝ)) = (6 / 5 : ℝ) by norm_num, show ((123 : ℝ) / (100 : ℝ)) = (123 / 100 : ℝ) by norm_num] using cell_01_anti (mu := mu)
  have h_1 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (123 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_0 hc_1
  have hc_2 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (123 / 100 : ℝ) (63 / 50 : ℝ)) := by
    simpa only [show ((123 : ℝ) / (100 : ℝ)) = (123 / 100 : ℝ) by norm_num, show ((126 : ℝ) / (100 : ℝ)) = (63 / 50 : ℝ) by norm_num] using cell_02_anti (mu := mu)
  have h_2 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (63 / 50 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_1 hc_2
  have hc_3 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (63 / 50 : ℝ) (129 / 100 : ℝ)) := by
    simpa only [show ((126 : ℝ) / (100 : ℝ)) = (63 / 50 : ℝ) by norm_num, show ((129 : ℝ) / (100 : ℝ)) = (129 / 100 : ℝ) by norm_num] using cell_03_anti (mu := mu)
  have h_3 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (129 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_2 hc_3
  have hc_4 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (129 / 100 : ℝ) (33 / 25 : ℝ)) := by
    simpa only [show ((129 : ℝ) / (100 : ℝ)) = (129 / 100 : ℝ) by norm_num, show ((132 : ℝ) / (100 : ℝ)) = (33 / 25 : ℝ) by norm_num] using cell_04_anti (mu := mu)
  have h_4 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (33 / 25 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_3 hc_4
  have hc_5 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (33 / 25 : ℝ) (27 / 20 : ℝ)) := by
    simpa only [show ((132 : ℝ) / (100 : ℝ)) = (33 / 25 : ℝ) by norm_num, show ((135 : ℝ) / (100 : ℝ)) = (27 / 20 : ℝ) by norm_num] using cell_05_anti (mu := mu)
  have h_5 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (27 / 20 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_4 hc_5
  have hc_6 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (27 / 20 : ℝ) (69 / 50 : ℝ)) := by
    simpa only [show ((135 : ℝ) / (100 : ℝ)) = (27 / 20 : ℝ) by norm_num, show ((138 : ℝ) / (100 : ℝ)) = (69 / 50 : ℝ) by norm_num] using cell_06_anti (mu := mu)
  have h_6 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (69 / 50 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_5 hc_6
  have hc_7 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (69 / 50 : ℝ) (141 / 100 : ℝ)) := by
    simpa only [show ((138 : ℝ) / (100 : ℝ)) = (69 / 50 : ℝ) by norm_num, show ((141 : ℝ) / (100 : ℝ)) = (141 / 100 : ℝ) by norm_num] using cell_07_anti (mu := mu)
  have h_7 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (141 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_6 hc_7
  have hc_8 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (141 / 100 : ℝ) (36 / 25 : ℝ)) := by
    simpa only [show ((141 : ℝ) / (100 : ℝ)) = (141 / 100 : ℝ) by norm_num, show ((144 : ℝ) / (100 : ℝ)) = (36 / 25 : ℝ) by norm_num] using cell_08_anti (mu := mu)
  have h_8 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (36 / 25 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_7 hc_8
  have hc_9 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (36 / 25 : ℝ) (147 / 100 : ℝ)) := by
    simpa only [show ((144 : ℝ) / (100 : ℝ)) = (36 / 25 : ℝ) by norm_num, show ((147 : ℝ) / (100 : ℝ)) = (147 / 100 : ℝ) by norm_num] using cell_09_anti (mu := mu)
  have h_9 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (147 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_8 hc_9
  have hc_10 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (147 / 100 : ℝ) (3 / 2 : ℝ)) := by
    simpa only [show ((147 : ℝ) / (100 : ℝ)) = (147 / 100 : ℝ) by norm_num, show ((150 : ℝ) / (100 : ℝ)) = (3 / 2 : ℝ) by norm_num] using cell_10_anti (mu := mu)
  have h_10 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (3 / 2 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_9 hc_10
  have hc_11 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (3 / 2 : ℝ) (153 / 100 : ℝ)) := by
    simpa only [show ((150 : ℝ) / (100 : ℝ)) = (3 / 2 : ℝ) by norm_num, show ((153 : ℝ) / (100 : ℝ)) = (153 / 100 : ℝ) by norm_num] using cell_11_anti (mu := mu)
  have h_11 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (153 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_10 hc_11
  have hc_12 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (153 / 100 : ℝ) (39 / 25 : ℝ)) := by
    simpa only [show ((153 : ℝ) / (100 : ℝ)) = (153 / 100 : ℝ) by norm_num, show ((156 : ℝ) / (100 : ℝ)) = (39 / 25 : ℝ) by norm_num] using cell_12_anti (mu := mu)
  have h_12 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (39 / 25 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_11 hc_12
  have hc_13 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (39 / 25 : ℝ) (159 / 100 : ℝ)) := by
    simpa only [show ((156 : ℝ) / (100 : ℝ)) = (39 / 25 : ℝ) by norm_num, show ((159 : ℝ) / (100 : ℝ)) = (159 / 100 : ℝ) by norm_num] using cell_13_anti (mu := mu)
  have h_13 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (159 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_12 hc_13
  have hc_14 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (159 / 100 : ℝ) (81 / 50 : ℝ)) := by
    simpa only [show ((159 : ℝ) / (100 : ℝ)) = (159 / 100 : ℝ) by norm_num, show ((162 : ℝ) / (100 : ℝ)) = (81 / 50 : ℝ) by norm_num] using cell_14_anti (mu := mu)
  have h_14 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (81 / 50 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_13 hc_14
  have hc_15 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (81 / 50 : ℝ) (33 / 20 : ℝ)) := by
    simpa only [show ((162 : ℝ) / (100 : ℝ)) = (81 / 50 : ℝ) by norm_num, show ((165 : ℝ) / (100 : ℝ)) = (33 / 20 : ℝ) by norm_num] using cell_15_anti (mu := mu)
  have h_15 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (33 / 20 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_14 hc_15
  have hc_16 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (33 / 20 : ℝ) (167 / 100 : ℝ)) := by
    simpa only [show ((165 : ℝ) / (100 : ℝ)) = (33 / 20 : ℝ) by norm_num, show ((167 : ℝ) / (100 : ℝ)) = (167 / 100 : ℝ) by norm_num] using cell_16_anti (mu := mu)
  have h_16 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (167 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_15 hc_16
  have hc_17 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (167 / 100 : ℝ) (42 / 25 : ℝ)) := by
    simpa only [show ((167 : ℝ) / (100 : ℝ)) = (167 / 100 : ℝ) by norm_num, show ((168 : ℝ) / (100 : ℝ)) = (42 / 25 : ℝ) by norm_num] using cell_17_anti (mu := mu)
  have h_17 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (42 / 25 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_16 hc_17
  have hc_18 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (42 / 25 : ℝ) (339 / 200 : ℝ)) := by
    simpa only [show ((336 : ℝ) / (200 : ℝ)) = (42 / 25 : ℝ) by norm_num, show ((339 : ℝ) / (200 : ℝ)) = (339 / 200 : ℝ) by norm_num] using cell_18_anti (mu := mu)
  have h_18 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (339 / 200 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_17 hc_18
  have hc_19 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (339 / 200 : ℝ) (341 / 200 : ℝ)) := by
    simpa only [show ((339 : ℝ) / (200 : ℝ)) = (339 / 200 : ℝ) by norm_num, show ((341 : ℝ) / (200 : ℝ)) = (341 / 200 : ℝ) by norm_num] using cell_19_anti (mu := mu)
  have h_19 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (341 / 200 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_18 hc_19
  have hc_20 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (341 / 200 : ℝ) (171 / 100 : ℝ)) := by
    simpa only [show ((341 : ℝ) / (200 : ℝ)) = (341 / 200 : ℝ) by norm_num, show ((342 : ℝ) / (200 : ℝ)) = (171 / 100 : ℝ) by norm_num] using cell_20_anti (mu := mu)
  have h_20 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (171 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_19 hc_20
  have hc_21 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (171 / 100 : ℝ) (137 / 80 : ℝ)) := by
    simpa only [show ((684 : ℝ) / (400 : ℝ)) = (171 / 100 : ℝ) by norm_num, show ((685 : ℝ) / (400 : ℝ)) = (137 / 80 : ℝ) by norm_num] using cell_21_anti (mu := mu)
  have h_21 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (137 / 80 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_20 hc_21
  have hc_22 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (137 / 80 : ℝ) (343 / 200 : ℝ)) := by
    simpa only [show ((685 : ℝ) / (400 : ℝ)) = (137 / 80 : ℝ) by norm_num, show ((686 : ℝ) / (400 : ℝ)) = (343 / 200 : ℝ) by norm_num] using cell_22_anti (mu := mu)
  have h_22 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (343 / 200 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_21 hc_22
  have hc_23 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (343 / 200 : ℝ) (43 / 25 : ℝ)) := by
    simpa only [show ((343 : ℝ) / (200 : ℝ)) = (343 / 200 : ℝ) by norm_num, show ((344 : ℝ) / (200 : ℝ)) = (43 / 25 : ℝ) by norm_num] using cell_23_anti (mu := mu)
  have h_23 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (43 / 25 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_22 hc_23
  have hc_24 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (43 / 25 : ℝ) (69 / 40 : ℝ)) := by
    simpa only [show ((344 : ℝ) / (200 : ℝ)) = (43 / 25 : ℝ) by norm_num, show ((345 : ℝ) / (200 : ℝ)) = (69 / 40 : ℝ) by norm_num] using cell_24_anti (mu := mu)
  have h_24 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (69 / 40 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_23 hc_24
  have hc_25 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (69 / 40 : ℝ) (691 / 400 : ℝ)) := by
    simpa only [show ((690 : ℝ) / (400 : ℝ)) = (69 / 40 : ℝ) by norm_num, show ((691 : ℝ) / (400 : ℝ)) = (691 / 400 : ℝ) by norm_num] using cell_25_anti (mu := mu)
  have h_25 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (691 / 400 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_24 hc_25
  have hc_26 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (691 / 400 : ℝ) (173 / 100 : ℝ)) := by
    simpa only [show ((691 : ℝ) / (400 : ℝ)) = (691 / 400 : ℝ) by norm_num, show ((692 : ℝ) / (400 : ℝ)) = (173 / 100 : ℝ) by norm_num] using cell_26_anti (mu := mu)
  have h_26 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (173 / 100 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_25 hc_26
  have hc_27 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (173 / 100 : ℝ) (693 / 400 : ℝ)) := by
    simpa only [show ((692 : ℝ) / (400 : ℝ)) = (173 / 100 : ℝ) by norm_num, show ((693 : ℝ) / (400 : ℝ)) = (693 / 400 : ℝ) by norm_num] using cell_27_anti (mu := mu)
  have h_27 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (693 / 400 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_26 hc_27
  have hc_28 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (693 / 400 : ℝ) (139 / 80 : ℝ)) := by
    simpa only [show ((693 : ℝ) / (400 : ℝ)) = (693 / 400 : ℝ) by norm_num, show ((695 : ℝ) / (400 : ℝ)) = (139 / 80 : ℝ) by norm_num] using cell_28_anti (mu := mu)
  have h_28 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (139 / 80 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_27 hc_28
  have hc_29 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (139 / 80 : ℝ) (697 / 400 : ℝ)) := by
    simpa only [show ((695 : ℝ) / (400 : ℝ)) = (139 / 80 : ℝ) by norm_num, show ((697 : ℝ) / (400 : ℝ)) = (697 / 400 : ℝ) by norm_num] using cell_29_anti (mu := mu)
  have h_29 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (697 / 400 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_28 hc_29
  have hc_30 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (697 / 400 : ℝ) (699 / 400 : ℝ)) := by
    simpa only [show ((697 : ℝ) / (400 : ℝ)) = (697 / 400 : ℝ) by norm_num, show ((699 : ℝ) / (400 : ℝ)) = (699 / 400 : ℝ) by norm_num] using cell_30_anti (mu := mu)
  have h_30 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (699 / 400 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_29 hc_30
  have hc_31 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (699 / 400 : ℝ) (7 / 4 : ℝ)) := by
    simpa only [show ((699 : ℝ) / (400 : ℝ)) = (699 / 400 : ℝ) by norm_num, show ((700 : ℝ) / (400 : ℝ)) = (7 / 4 : ℝ) by norm_num] using cell_31_anti (mu := mu)
  have h_31 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (7 / 4 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_30 hc_31
  have hc_32 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (7 / 4 : ℝ) (701 / 400 : ℝ)) := by
    simpa only [show ((700 : ℝ) / (400 : ℝ)) = (7 / 4 : ℝ) by norm_num, show ((701 : ℝ) / (400 : ℝ)) = (701 / 400 : ℝ) by norm_num] using cell_32_anti (mu := mu)
  have h_32 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (701 / 400 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_31 hc_32
  have hc_33 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (701 / 400 : ℝ) (351 / 200 : ℝ)) := by
    simpa only [show ((701 : ℝ) / (400 : ℝ)) = (701 / 400 : ℝ) by norm_num, show ((702 : ℝ) / (400 : ℝ)) = (351 / 200 : ℝ) by norm_num] using cell_33_anti (mu := mu)
  have h_33 : StrictAntiOn (fun lam => RFunc mu lam / lam) (Set.Icc (117 / 100 : ℝ) (351 / 200 : ℝ)) :=
    strictAntiOn_Icc_glue (by norm_num) (by norm_num) h_32 hc_33
  exact h_33

end GWSpeedCertificate.Certs
