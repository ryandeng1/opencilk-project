; RUN: opt -S %s -passes=inline -enable-drf-aa -enable-drf-aa-sibling-witness | FileCheck %s --check-prefix=BONUS
; RUN: opt -S %s -passes=inline -enable-drf-aa | FileCheck %s --check-prefix=PLAIN
; RUN: opt -S %s -passes=inline -enable-drf-aa -enable-drf-aa-sibling-witness -drf-aa-sibling-witness-inline-threshold=0 | FileCheck %s --check-prefix=PLAIN

; A spawned self-call with a literal size, and the continuation's self-call
; with a literal size, are the base cases of a divide-and-conquer recursion.
; With the sibling witness enabled they get the dedicated inline threshold so
; the leaves are exposed to the proof; the non-literal recursive calls in the
; general branch keep the ordinary threshold. The leaf below costs more than
; the default threshold, so without the witness nothing is inlined.

; BONUS-LABEL: define void @rec(
; BONUS-NOT: call void @rec(ptr {.*}, i64 1)
; BONUS: call void @rec(ptr %a, i64 %h)
; BONUS: call void @rec(ptr %a.hi, i64 %h)
; PLAIN-LABEL: define void @rec(
; PLAIN: call void @rec(ptr %a, i64 1)
; PLAIN: call void @rec(ptr %a.hi, i64 1)
; PLAIN: call void @rec(ptr %a, i64 %h)
define void @rec(ptr %a, i64 %n) {
entry:
  %sr = call token @llvm.syncregion.start()
  %leaf = icmp eq i64 %n, 1
  br i1 %leaf, label %base, label %split
base:
  %p0 = getelementptr i32, ptr %a, i64 0
  %x0 = load i32, ptr %p0
  %y0 = mul i32 %x0, 3
  store i32 %y0, ptr %p0
  %p1 = getelementptr i32, ptr %a, i64 1
  %x1 = load i32, ptr %p1
  %y1 = mul i32 %x1, 4
  store i32 %y1, ptr %p1
  %p2 = getelementptr i32, ptr %a, i64 2
  %x2 = load i32, ptr %p2
  %y2 = mul i32 %x2, 5
  store i32 %y2, ptr %p2
  %p3 = getelementptr i32, ptr %a, i64 3
  %x3 = load i32, ptr %p3
  %y3 = mul i32 %x3, 6
  store i32 %y3, ptr %p3
  %p4 = getelementptr i32, ptr %a, i64 4
  %x4 = load i32, ptr %p4
  %y4 = mul i32 %x4, 7
  store i32 %y4, ptr %p4
  %p5 = getelementptr i32, ptr %a, i64 5
  %x5 = load i32, ptr %p5
  %y5 = mul i32 %x5, 8
  store i32 %y5, ptr %p5
  %p6 = getelementptr i32, ptr %a, i64 6
  %x6 = load i32, ptr %p6
  %y6 = mul i32 %x6, 9
  store i32 %y6, ptr %p6
  %p7 = getelementptr i32, ptr %a, i64 7
  %x7 = load i32, ptr %p7
  %y7 = mul i32 %x7, 10
  store i32 %y7, ptr %p7
  %p8 = getelementptr i32, ptr %a, i64 8
  %x8 = load i32, ptr %p8
  %y8 = mul i32 %x8, 11
  store i32 %y8, ptr %p8
  %p9 = getelementptr i32, ptr %a, i64 9
  %x9 = load i32, ptr %p9
  %y9 = mul i32 %x9, 12
  store i32 %y9, ptr %p9
  %p10 = getelementptr i32, ptr %a, i64 10
  %x10 = load i32, ptr %p10
  %y10 = mul i32 %x10, 13
  store i32 %y10, ptr %p10
  %p11 = getelementptr i32, ptr %a, i64 11
  %x11 = load i32, ptr %p11
  %y11 = mul i32 %x11, 14
  store i32 %y11, ptr %p11
  %p12 = getelementptr i32, ptr %a, i64 12
  %x12 = load i32, ptr %p12
  %y12 = mul i32 %x12, 15
  store i32 %y12, ptr %p12
  %p13 = getelementptr i32, ptr %a, i64 13
  %x13 = load i32, ptr %p13
  %y13 = mul i32 %x13, 16
  store i32 %y13, ptr %p13
  %p14 = getelementptr i32, ptr %a, i64 14
  %x14 = load i32, ptr %p14
  %y14 = mul i32 %x14, 17
  store i32 %y14, ptr %p14
  %p15 = getelementptr i32, ptr %a, i64 15
  %x15 = load i32, ptr %p15
  %y15 = mul i32 %x15, 18
  store i32 %y15, ptr %p15
  %p16 = getelementptr i32, ptr %a, i64 16
  %x16 = load i32, ptr %p16
  %y16 = mul i32 %x16, 19
  store i32 %y16, ptr %p16
  %p17 = getelementptr i32, ptr %a, i64 17
  %x17 = load i32, ptr %p17
  %y17 = mul i32 %x17, 20
  store i32 %y17, ptr %p17
  %p18 = getelementptr i32, ptr %a, i64 18
  %x18 = load i32, ptr %p18
  %y18 = mul i32 %x18, 21
  store i32 %y18, ptr %p18
  %p19 = getelementptr i32, ptr %a, i64 19
  %x19 = load i32, ptr %p19
  %y19 = mul i32 %x19, 22
  store i32 %y19, ptr %p19
  %p20 = getelementptr i32, ptr %a, i64 20
  %x20 = load i32, ptr %p20
  %y20 = mul i32 %x20, 23
  store i32 %y20, ptr %p20
  %p21 = getelementptr i32, ptr %a, i64 21
  %x21 = load i32, ptr %p21
  %y21 = mul i32 %x21, 24
  store i32 %y21, ptr %p21
  %p22 = getelementptr i32, ptr %a, i64 22
  %x22 = load i32, ptr %p22
  %y22 = mul i32 %x22, 25
  store i32 %y22, ptr %p22
  %p23 = getelementptr i32, ptr %a, i64 23
  %x23 = load i32, ptr %p23
  %y23 = mul i32 %x23, 26
  store i32 %y23, ptr %p23
  %p24 = getelementptr i32, ptr %a, i64 24
  %x24 = load i32, ptr %p24
  %y24 = mul i32 %x24, 27
  store i32 %y24, ptr %p24
  %p25 = getelementptr i32, ptr %a, i64 25
  %x25 = load i32, ptr %p25
  %y25 = mul i32 %x25, 28
  store i32 %y25, ptr %p25
  %p26 = getelementptr i32, ptr %a, i64 26
  %x26 = load i32, ptr %p26
  %y26 = mul i32 %x26, 29
  store i32 %y26, ptr %p26
  %p27 = getelementptr i32, ptr %a, i64 27
  %x27 = load i32, ptr %p27
  %y27 = mul i32 %x27, 30
  store i32 %y27, ptr %p27
  %p28 = getelementptr i32, ptr %a, i64 28
  %x28 = load i32, ptr %p28
  %y28 = mul i32 %x28, 31
  store i32 %y28, ptr %p28
  %p29 = getelementptr i32, ptr %a, i64 29
  %x29 = load i32, ptr %p29
  %y29 = mul i32 %x29, 32
  store i32 %y29, ptr %p29
  %p30 = getelementptr i32, ptr %a, i64 30
  %x30 = load i32, ptr %p30
  %y30 = mul i32 %x30, 33
  store i32 %y30, ptr %p30
  %p31 = getelementptr i32, ptr %a, i64 31
  %x31 = load i32, ptr %p31
  %y31 = mul i32 %x31, 34
  store i32 %y31, ptr %p31
  %p32 = getelementptr i32, ptr %a, i64 32
  %x32 = load i32, ptr %p32
  %y32 = mul i32 %x32, 35
  store i32 %y32, ptr %p32
  %p33 = getelementptr i32, ptr %a, i64 33
  %x33 = load i32, ptr %p33
  %y33 = mul i32 %x33, 36
  store i32 %y33, ptr %p33
  %p34 = getelementptr i32, ptr %a, i64 34
  %x34 = load i32, ptr %p34
  %y34 = mul i32 %x34, 37
  store i32 %y34, ptr %p34
  %p35 = getelementptr i32, ptr %a, i64 35
  %x35 = load i32, ptr %p35
  %y35 = mul i32 %x35, 38
  store i32 %y35, ptr %p35
  %p36 = getelementptr i32, ptr %a, i64 36
  %x36 = load i32, ptr %p36
  %y36 = mul i32 %x36, 39
  store i32 %y36, ptr %p36
  %p37 = getelementptr i32, ptr %a, i64 37
  %x37 = load i32, ptr %p37
  %y37 = mul i32 %x37, 40
  store i32 %y37, ptr %p37
  %p38 = getelementptr i32, ptr %a, i64 38
  %x38 = load i32, ptr %p38
  %y38 = mul i32 %x38, 41
  store i32 %y38, ptr %p38
  %p39 = getelementptr i32, ptr %a, i64 39
  %x39 = load i32, ptr %p39
  %y39 = mul i32 %x39, 42
  store i32 %y39, ptr %p39
  %p40 = getelementptr i32, ptr %a, i64 40
  %x40 = load i32, ptr %p40
  %y40 = mul i32 %x40, 43
  store i32 %y40, ptr %p40
  %p41 = getelementptr i32, ptr %a, i64 41
  %x41 = load i32, ptr %p41
  %y41 = mul i32 %x41, 44
  store i32 %y41, ptr %p41
  %p42 = getelementptr i32, ptr %a, i64 42
  %x42 = load i32, ptr %p42
  %y42 = mul i32 %x42, 45
  store i32 %y42, ptr %p42
  %p43 = getelementptr i32, ptr %a, i64 43
  %x43 = load i32, ptr %p43
  %y43 = mul i32 %x43, 46
  store i32 %y43, ptr %p43
  %p44 = getelementptr i32, ptr %a, i64 44
  %x44 = load i32, ptr %p44
  %y44 = mul i32 %x44, 47
  store i32 %y44, ptr %p44
  %p45 = getelementptr i32, ptr %a, i64 45
  %x45 = load i32, ptr %p45
  %y45 = mul i32 %x45, 48
  store i32 %y45, ptr %p45
  %p46 = getelementptr i32, ptr %a, i64 46
  %x46 = load i32, ptr %p46
  %y46 = mul i32 %x46, 49
  store i32 %y46, ptr %p46
  %p47 = getelementptr i32, ptr %a, i64 47
  %x47 = load i32, ptr %p47
  %y47 = mul i32 %x47, 50
  store i32 %y47, ptr %p47
  %p48 = getelementptr i32, ptr %a, i64 48
  %x48 = load i32, ptr %p48
  %y48 = mul i32 %x48, 51
  store i32 %y48, ptr %p48
  %p49 = getelementptr i32, ptr %a, i64 49
  %x49 = load i32, ptr %p49
  %y49 = mul i32 %x49, 52
  store i32 %y49, ptr %p49
  %p50 = getelementptr i32, ptr %a, i64 50
  %x50 = load i32, ptr %p50
  %y50 = mul i32 %x50, 53
  store i32 %y50, ptr %p50
  %p51 = getelementptr i32, ptr %a, i64 51
  %x51 = load i32, ptr %p51
  %y51 = mul i32 %x51, 54
  store i32 %y51, ptr %p51
  %p52 = getelementptr i32, ptr %a, i64 52
  %x52 = load i32, ptr %p52
  %y52 = mul i32 %x52, 55
  store i32 %y52, ptr %p52
  %p53 = getelementptr i32, ptr %a, i64 53
  %x53 = load i32, ptr %p53
  %y53 = mul i32 %x53, 56
  store i32 %y53, ptr %p53
  %p54 = getelementptr i32, ptr %a, i64 54
  %x54 = load i32, ptr %p54
  %y54 = mul i32 %x54, 57
  store i32 %y54, ptr %p54
  %p55 = getelementptr i32, ptr %a, i64 55
  %x55 = load i32, ptr %p55
  %y55 = mul i32 %x55, 58
  store i32 %y55, ptr %p55
  %p56 = getelementptr i32, ptr %a, i64 56
  %x56 = load i32, ptr %p56
  %y56 = mul i32 %x56, 59
  store i32 %y56, ptr %p56
  %p57 = getelementptr i32, ptr %a, i64 57
  %x57 = load i32, ptr %p57
  %y57 = mul i32 %x57, 60
  store i32 %y57, ptr %p57
  %p58 = getelementptr i32, ptr %a, i64 58
  %x58 = load i32, ptr %p58
  %y58 = mul i32 %x58, 61
  store i32 %y58, ptr %p58
  %p59 = getelementptr i32, ptr %a, i64 59
  %x59 = load i32, ptr %p59
  %y59 = mul i32 %x59, 62
  store i32 %y59, ptr %p59
  %p60 = getelementptr i32, ptr %a, i64 60
  %x60 = load i32, ptr %p60
  %y60 = mul i32 %x60, 63
  store i32 %y60, ptr %p60
  %p61 = getelementptr i32, ptr %a, i64 61
  %x61 = load i32, ptr %p61
  %y61 = mul i32 %x61, 64
  store i32 %y61, ptr %p61
  %p62 = getelementptr i32, ptr %a, i64 62
  %x62 = load i32, ptr %p62
  %y62 = mul i32 %x62, 65
  store i32 %y62, ptr %p62
  %p63 = getelementptr i32, ptr %a, i64 63
  %x63 = load i32, ptr %p63
  %y63 = mul i32 %x63, 66
  store i32 %y63, ptr %p63
  %p64 = getelementptr i32, ptr %a, i64 64
  %x64 = load i32, ptr %p64
  %y64 = mul i32 %x64, 67
  store i32 %y64, ptr %p64
  %p65 = getelementptr i32, ptr %a, i64 65
  %x65 = load i32, ptr %p65
  %y65 = mul i32 %x65, 68
  store i32 %y65, ptr %p65
  %p66 = getelementptr i32, ptr %a, i64 66
  %x66 = load i32, ptr %p66
  %y66 = mul i32 %x66, 69
  store i32 %y66, ptr %p66
  %p67 = getelementptr i32, ptr %a, i64 67
  %x67 = load i32, ptr %p67
  %y67 = mul i32 %x67, 70
  store i32 %y67, ptr %p67
  %p68 = getelementptr i32, ptr %a, i64 68
  %x68 = load i32, ptr %p68
  %y68 = mul i32 %x68, 71
  store i32 %y68, ptr %p68
  %p69 = getelementptr i32, ptr %a, i64 69
  %x69 = load i32, ptr %p69
  %y69 = mul i32 %x69, 72
  store i32 %y69, ptr %p69
  ret void
split:
  %h = lshr i64 %n, 1
  %two = icmp eq i64 %n, 2
  %a.hi = getelementptr i32, ptr %a, i64 128
  br i1 %two, label %phase, label %general
phase:
  detach within %sr, label %det, label %cont
det:
  call void @rec(ptr %a, i64 1)
  reattach within %sr, label %cont
cont:
  call void @rec(ptr %a.hi, i64 1)
  sync within %sr, label %done
general:
  detach within %sr, label %gdet, label %gcont
gdet:
  call void @rec(ptr %a, i64 %h)
  reattach within %sr, label %gcont
gcont:
  call void @rec(ptr %a.hi, i64 %h)
  sync within %sr, label %done
done:
  ret void
}

declare token @llvm.syncregion.start()
