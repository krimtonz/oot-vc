glabel func_800B9568
/* 800B9568 000B4B28  94 21 FF D0 */	stwu r1, -0x30(r1)
/* 800B956C 000B4B2C  7C 08 02 A6 */	mflr r0
/* 800B9570 000B4B30  90 01 00 34 */	stw r0, 0x34(r1)
/* 800B9574 000B4B34  39 61 00 30 */	addi r11, r1, 0x30
/* 800B9578 000B4B38  48 09 98 D5 */	bl _savegpr_24
/* 800B957C 000B4B3C  34 01 00 08 */	addic. r0, r1, 8
/* 800B9580 000B4B40  7C 78 1B 78 */	mr r24, r3
/* 800B9584 000B4B44  7C 99 23 78 */	mr r25, r4
/* 800B9588 000B4B48  7C BA 2B 78 */	mr r26, r5
/* 800B958C 000B4B4C  7C DB 33 78 */	mr r27, r6
/* 800B9590 000B4B50  7C FC 3B 78 */	mr r28, r7
/* 800B9594 000B4B54  7D 1D 43 78 */	mr r29, r8
/* 800B9598 000B4B58  7D 3E 4B 78 */	mr r30, r9
/* 800B959C 000B4B5C  3B E0 00 00 */	li r31, 0
/* 800B95A0 000B4B60  40 82 00 0C */	bne lbl_800B95AC
/* 800B95A4 000B4B64  3B E0 FF FC */	li r31, -4
/* 800B95A8 000B4B68  48 00 00 4C */	b lbl_800B95F4
lbl_800B95AC:
/* 800B95AC 000B4B6C  80 6D 85 04 */	lwz r3, lbl_8025CBC4-_SDA_BASE_(r13)
/* 800B95B0 000B4B70  38 80 00 40 */	li r4, 0x40
/* 800B95B4 000B4B74  38 A0 00 20 */	li r5, 0x20
/* 800B95B8 000B4B78  48 00 05 8D */	bl func_800B9B44
/* 800B95BC 000B4B7C  2C 03 00 00 */	cmpwi r3, 0
/* 800B95C0 000B4B80  90 61 00 08 */	stw r3, 8(r1)
/* 800B95C4 000B4B84  40 82 00 0C */	bne lbl_800B95D0
/* 800B95C8 000B4B88  3B E0 FF EA */	li r31, -22
/* 800B95CC 000B4B8C  48 00 00 28 */	b lbl_800B95F4
lbl_800B95D0:
/* 800B95D0 000B4B90  93 A3 00 20 */	stw r29, 0x20(r3)
/* 800B95D4 000B4B94  38 A0 00 00 */	li r5, 0
/* 800B95D8 000B4B98  38 00 00 07 */	li r0, 7
/* 800B95DC 000B4B9C  80 81 00 08 */	lwz r4, 8(r1)
/* 800B95E0 000B4BA0  93 C4 00 24 */	stw r30, 0x24(r4)
/* 800B95E4 000B4BA4  80 81 00 08 */	lwz r4, 8(r1)
/* 800B95E8 000B4BA8  90 A4 00 28 */	stw r5, 0x28(r4)
/* 800B95EC 000B4BAC  90 03 00 00 */	stw r0, 0(r3)
/* 800B95F0 000B4BB0  93 03 00 08 */	stw r24, 8(r3)
lbl_800B95F4:
/* 800B95F4 000B4BB4  2C 1F 00 00 */	cmpwi r31, 0
/* 800B95F8 000B4BB8  40 82 00 38 */	bne lbl_800B9630
/* 800B95FC 000B4BBC  80 61 00 08 */	lwz r3, 8(r1)
/* 800B9600 000B4BC0  7F 24 CB 78 */	mr r4, r25
/* 800B9604 000B4BC4  7F 45 D3 78 */	mr r5, r26
/* 800B9608 000B4BC8  7F 66 DB 78 */	mr r6, r27
/* 800B960C 000B4BCC  7F 87 E3 78 */	mr r7, r28
/* 800B9610 000B4BD0  4B FF FE 1D */	bl func_800B942C
/* 800B9614 000B4BD4  2C 03 00 00 */	cmpwi r3, 0
/* 800B9618 000B4BD8  7C 7F 1B 78 */	mr r31, r3
/* 800B961C 000B4BDC  40 82 00 14 */	bne lbl_800B9630
/* 800B9620 000B4BE0  80 61 00 08 */	lwz r3, 8(r1)
/* 800B9624 000B4BE4  7F A4 EB 78 */	mr r4, r29
/* 800B9628 000B4BE8  4B FF EF D9 */	bl func_800B8600
/* 800B962C 000B4BEC  7C 7F 1B 78 */	mr r31, r3
lbl_800B9630:
/* 800B9630 000B4BF0  39 61 00 30 */	addi r11, r1, 0x30
/* 800B9634 000B4BF4  7F E3 FB 78 */	mr r3, r31
/* 800B9638 000B4BF8  48 09 98 61 */	bl _restgpr_24
/* 800B963C 000B4BFC  80 01 00 34 */	lwz r0, 0x34(r1)
/* 800B9640 000B4C00  7C 08 03 A6 */	mtlr r0
/* 800B9644 000B4C04  38 21 00 30 */	addi r1, r1, 0x30
/* 800B9648 000B4C08  4E 80 00 20 */	blr 
