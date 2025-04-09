; ModuleID = 'tmp/tmp_ir_source0.ll'
source_filename = "examples/concepts/llvm/pallas/pallas_c_assume.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@llvm.used = appending global [5 x ptr] [ptr @PALLAS_SPEC_0, ptr @PALLAS_SPEC_1, ptr @PALLAS_SPEC_2, ptr @PALLAS_SPEC_3, ptr @PALLAS_SPEC_4], section "llvm.metadata"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @foo(i32 noundef %0, i32 noundef %1) #0 !dbg !12 !pallas.fcontract !17 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !21, metadata !DIExpression()), !dbg !23
  call void @llvm.dbg.value(metadata i32 %1, metadata !22, metadata !DIExpression()), !dbg !23
  call void @llvm.dbg.value(metadata i32 %0, metadata !24, metadata !DIExpression()), !dbg !23
  %3 = icmp sgt i32 %0, %1, !dbg !25, !pallas.stmntBlock !27
  br i1 %3, label %4, label %6, !dbg !31

4:                                                ; preds = %2
  %5 = add nsw i32 %0, 1, !dbg !32
  call void @llvm.dbg.value(metadata i32 %5, metadata !21, metadata !DIExpression()), !dbg !23
  br label %8, !dbg !34

6:                                                ; preds = %2
  %7 = add nsw i32 %1, 1, !dbg !35
  call void @llvm.dbg.value(metadata i32 %7, metadata !22, metadata !DIExpression()), !dbg !23
  br label %8

8:                                                ; preds = %6, %4
  %.01 = phi i32 [ %1, %4 ], [ %7, %6 ]
  %.0 = phi i32 [ %5, %4 ], [ %0, %6 ]
  call void @llvm.dbg.value(metadata i32 %.0, metadata !21, metadata !DIExpression()), !dbg !23
  call void @llvm.dbg.value(metadata i32 %.01, metadata !22, metadata !DIExpression()), !dbg !23
  %9 = add nsw i32 %0, %.01, !dbg !37, !pallas.stmntBlock !38
  call void @llvm.dbg.value(metadata i32 %9, metadata !24, metadata !DIExpression()), !dbg !23
  %10 = add nsw i32 %.0, %.01, !dbg !42
  ret i32 %10, !dbg !43
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @bar(i32 noundef %0, i32 noundef %1) #0 !dbg !44 !pallas.fcontract !45 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !49, metadata !DIExpression()), !dbg !51
  call void @llvm.dbg.value(metadata i32 %1, metadata !50, metadata !DIExpression()), !dbg !51
  call void @llvm.dbg.value(metadata i32 %0, metadata !52, metadata !DIExpression()), !dbg !51
  %3 = sub nsw i32 %0, %1, !dbg !53, !pallas.stmntBlock !54
  call void @llvm.dbg.value(metadata i32 %3, metadata !52, metadata !DIExpression()), !dbg !51
  ret i32 %3, !dbg !58
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare void @llvm.dbg.value(metadata, metadata, metadata) #1

; Function Attrs: noinline nounwind uwtable
define dso_local zeroext i1 @PALLAS_SPEC_0(i32 noundef %0, i32 noundef %1) #0 !dbg !59 !pallas.exprWrapper !63 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !64, metadata !DIExpression()), !dbg !65
  call void @llvm.dbg.value(metadata i32 %1, metadata !66, metadata !DIExpression()), !dbg !65
  %3 = icmp sgt i32 %0, 0, !dbg !67
  br i1 %3, label %4, label %6, !dbg !68

4:                                                ; preds = %2
  %5 = icmp sgt i32 %1, 0, !dbg !69
  br label %6

6:                                                ; preds = %4, %2
  %7 = phi i1 [ false, %2 ], [ %5, %4 ], !dbg !65
  ret i1 %7, !dbg !65
}

; Function Attrs: noinline nounwind uwtable
define dso_local zeroext i1 @PALLAS_SPEC_1(i32 noundef %0, i32 noundef %1) #0 !dbg !70 !pallas.exprWrapper !63 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !71, metadata !DIExpression()), !dbg !72
  call void @llvm.dbg.value(metadata i32 %1, metadata !73, metadata !DIExpression()), !dbg !72
  %3 = call i32 @pallas.result.0(), !dbg !74
  %4 = icmp sgt i32 %3, 0, !dbg !75
  ret i1 %4, !dbg !72
}

; Function Attrs: noinline nounwind uwtable
define dso_local zeroext i1 @PALLAS_SPEC_2(i32 noundef %0, i32 noundef %1, i32 noundef %2) #0 !dbg !76 !pallas.exprWrapper !63 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !79, metadata !DIExpression()), !dbg !80
  call void @llvm.dbg.value(metadata i32 %1, metadata !81, metadata !DIExpression()), !dbg !80
  call void @llvm.dbg.value(metadata i32 %2, metadata !82, metadata !DIExpression()), !dbg !80
  %4 = icmp slt i32 %2, 0, !dbg !83
  ret i1 %4, !dbg !80
}

; Function Attrs: noinline nounwind uwtable
define dso_local zeroext i1 @PALLAS_SPEC_3(i32 noundef %0, i32 noundef %1, i32 noundef %2) #0 !dbg !84 !pallas.exprWrapper !63 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !85, metadata !DIExpression()), !dbg !86
  call void @llvm.dbg.value(metadata i32 %1, metadata !87, metadata !DIExpression()), !dbg !86
  call void @llvm.dbg.value(metadata i32 %2, metadata !88, metadata !DIExpression()), !dbg !86
  ret i1 false, !dbg !86
}

; Function Attrs: noinline nounwind uwtable
define dso_local zeroext i1 @PALLAS_SPEC_4(i32 noundef %0, i32 noundef %1, i32 noundef %2) #0 !dbg !89 !pallas.exprWrapper !63 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !90, metadata !DIExpression()), !dbg !91
  call void @llvm.dbg.value(metadata i32 %1, metadata !92, metadata !DIExpression()), !dbg !91
  call void @llvm.dbg.value(metadata i32 %2, metadata !93, metadata !DIExpression()), !dbg !91
  %4 = icmp sgt i32 %0, %1, !dbg !94
  ret i1 %4, !dbg !91
}

declare !pallas.specLib !95 i32 @pallas.result.0()

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }

!llvm.dbg.cu = !{!0, !2}
!llvm.module.flags = !{!4, !5, !6, !7, !8, !9, !10}
!llvm.ident = !{!11, !11}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "clang version 17.0.0 (https://github.com/swiftlang/llvm-project.git 73500bf55acff5fa97b56dcdeb013f288efd084f)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "examples/concepts/llvm/pallas/pallas_c_assume.c", directory: ".", checksumkind: CSK_MD5, checksum: "bbc14bf93954288d50c471950a810f4d")
!2 = distinct !DICompileUnit(language: DW_LANG_C11, file: !3, producer: "clang version 17.0.0 (https://github.com/swiftlang/llvm-project.git 73500bf55acff5fa97b56dcdeb013f288efd084f)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "tmp/source_wrappers.c", directory: ".", checksumkind: CSK_MD5, checksum: "5c1e1599f044cc38b4f54a8cd4ab1837")
!4 = !{i32 7, !"Dwarf Version", i32 5}
!5 = !{i32 2, !"Debug Info Version", i32 3}
!6 = !{i32 1, !"wchar_size", i32 4}
!7 = !{i32 8, !"PIC Level", i32 2}
!8 = !{i32 7, !"PIE Level", i32 2}
!9 = !{i32 7, !"uwtable", i32 2}
!10 = !{i32 7, !"frame-pointer", i32 2}
!11 = !{!"clang version 17.0.0 (https://github.com/swiftlang/llvm-project.git 73500bf55acff5fa97b56dcdeb013f288efd084f)"}
!12 = distinct !DISubprogram(name: "foo", scope: !1, file: !1, line: 13, type: !13, scopeLine: 13, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !16)
!13 = !DISubroutineType(types: !14)
!14 = !{!15, !15, !15}
!15 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!16 = !{}
!17 = !{!18, i1 false, !19}
!18 = !{!"pallas.srcLoc", i64 10, i64 1, i64 12, i64 1}
!19 = !{!"pallas.requires", !20, ptr @PALLAS_SPEC_0, !21, !22}
!20 = !{!"pallas.srcLoc", i64 11, i64 1, i64 11, i64 24}
!21 = !DILocalVariable(name: "a", arg: 1, scope: !12, file: !1, line: 13, type: !15)
!22 = !DILocalVariable(name: "b", arg: 2, scope: !12, file: !1, line: 13, type: !15)
!23 = !DILocation(line: 0, scope: !12)
!24 = !DILocalVariable(name: "tmp", scope: !12, file: !1, line: 14, type: !15)
!25 = !DILocation(line: 19, column: 11, scope: !26)
!26 = distinct !DILexicalBlock(scope: !12, file: !1, line: 19, column: 9)
!27 = !{!28, !29}
!28 = !{!"pallas.srcLoc", i64 16, i64 5, i64 18, i64 5}
!29 = !{!"pallas.assume", !30, ptr @PALLAS_SPEC_2, !21, !22, !24}
!30 = !{!"pallas.srcLoc", i64 17, i64 5, i64 17, i64 19}
!31 = !DILocation(line: 19, column: 9, scope: !12)
!32 = !DILocation(line: 20, column: 10, scope: !33)
!33 = distinct !DILexicalBlock(scope: !26, file: !1, line: 19, column: 16)
!34 = !DILocation(line: 21, column: 5, scope: !33)
!35 = !DILocation(line: 22, column: 10, scope: !36)
!36 = distinct !DILexicalBlock(scope: !26, file: !1, line: 21, column: 12)
!37 = !DILocation(line: 25, column: 9, scope: !12)
!38 = !{!39, !40}
!39 = !{!"pallas.srcLoc", i64 24, i64 5, i64 24, i64 23}
!40 = !{!"pallas.assert", !41, ptr @PALLAS_SPEC_3, !21, !22, !24}
!41 = !{!"pallas.srcLoc", i64 24, i64 9, i64 24, i64 21}
!42 = !DILocation(line: 26, column: 14, scope: !12)
!43 = !DILocation(line: 26, column: 5, scope: !12)
!44 = distinct !DISubprogram(name: "bar", scope: !1, file: !1, line: 32, type: !13, scopeLine: 32, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !16)
!45 = !{!46, i1 false, !47}
!46 = !{!"pallas.srcLoc", i64 29, i64 1, i64 31, i64 1}
!47 = !{!"pallas.ensures", !48, ptr @PALLAS_SPEC_1, !49, !50}
!48 = !{!"pallas.srcLoc", i64 30, i64 1, i64 30, i64 25}
!49 = !DILocalVariable(name: "a", arg: 1, scope: !44, file: !1, line: 32, type: !15)
!50 = !DILocalVariable(name: "b", arg: 2, scope: !44, file: !1, line: 32, type: !15)
!51 = !DILocation(line: 0, scope: !44)
!52 = !DILocalVariable(name: "tmp", scope: !44, file: !1, line: 33, type: !15)
!53 = !DILocation(line: 35, column: 9, scope: !44)
!54 = !{!55, !56}
!55 = !{!"pallas.srcLoc", i64 34, i64 5, i64 34, i64 23}
!56 = !{!"pallas.assume", !57, ptr @PALLAS_SPEC_4, !49, !50, !52}
!57 = !{!"pallas.srcLoc", i64 34, i64 9, i64 34, i64 21}
!58 = !DILocation(line: 36, column: 5, scope: !44)
!59 = distinct !DISubprogram(name: "PALLAS_SPEC_0", scope: !1, file: !1, line: 11, type: !60, scopeLine: 11, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !16)
!60 = !DISubroutineType(types: !61)
!61 = !{!62, !15, !15}
!62 = !DIBasicType(name: "_Bool", size: 8, encoding: DW_ATE_boolean)
!63 = !{!""}
!64 = !DILocalVariable(name: "a", arg: 1, scope: !59, file: !1, line: 11, type: !15)
!65 = !DILocation(line: 0, scope: !59)
!66 = !DILocalVariable(name: "b", arg: 2, scope: !59, file: !1, line: 11, type: !15)
!67 = !DILocation(line: 11, column: 12, scope: !59)
!68 = !DILocation(line: 11, column: 16, scope: !59)
!69 = !DILocation(line: 11, column: 21, scope: !59)
!70 = distinct !DISubprogram(name: "PALLAS_SPEC_1", scope: !1, file: !1, line: 30, type: !60, scopeLine: 30, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !16)
!71 = !DILocalVariable(name: "a", arg: 1, scope: !70, file: !1, line: 30, type: !15)
!72 = !DILocation(line: 0, scope: !70)
!73 = !DILocalVariable(name: "b", arg: 2, scope: !70, file: !1, line: 30, type: !15)
!74 = !DILocation(line: 30, column: 9, scope: !70)
!75 = !DILocation(line: 30, column: 22, scope: !70)
!76 = distinct !DISubprogram(name: "PALLAS_SPEC_2", scope: !1, file: !1, line: 17, type: !77, scopeLine: 17, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !16)
!77 = !DISubroutineType(types: !78)
!78 = !{!62, !15, !15, !15}
!79 = !DILocalVariable(name: "a", arg: 1, scope: !76, file: !1, line: 17, type: !15)
!80 = !DILocation(line: 0, scope: !76)
!81 = !DILocalVariable(name: "b", arg: 2, scope: !76, file: !1, line: 17, type: !15)
!82 = !DILocalVariable(name: "tmp", arg: 3, scope: !76, file: !1, line: 17, type: !15)
!83 = !DILocation(line: 17, column: 16, scope: !76)
!84 = distinct !DISubprogram(name: "PALLAS_SPEC_3", scope: !1, file: !1, line: 24, type: !77, scopeLine: 24, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !16)
!85 = !DILocalVariable(name: "a", arg: 1, scope: !84, file: !1, line: 24, type: !15)
!86 = !DILocation(line: 0, scope: !84)
!87 = !DILocalVariable(name: "b", arg: 2, scope: !84, file: !1, line: 24, type: !15)
!88 = !DILocalVariable(name: "tmp", arg: 3, scope: !84, file: !1, line: 24, type: !15)
!89 = distinct !DISubprogram(name: "PALLAS_SPEC_4", scope: !1, file: !1, line: 34, type: !77, scopeLine: 34, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !16)
!90 = !DILocalVariable(name: "a", arg: 1, scope: !89, file: !1, line: 34, type: !15)
!91 = !DILocation(line: 0, scope: !89)
!92 = !DILocalVariable(name: "b", arg: 2, scope: !89, file: !1, line: 34, type: !15)
!93 = !DILocalVariable(name: "tmp", arg: 3, scope: !89, file: !1, line: 34, type: !15)
!94 = !DILocation(line: 34, column: 18, scope: !89)
!95 = !{!"pallas.result"}
