glabel __cpuBreak
/* 8000E4A4 00009A64  80 03 00 00 */	lwz r0, 0(r3)
/* 8000E4A8 00009A68  60 00 00 02 */	ori r0, r0, 2
/* 8000E4AC 00009A6C  90 03 00 00 */	stw r0, 0(r3)
/* 8000E4B0 00009A70  38 60 00 01 */	li r3, 1
/* 8000E4B4 00009A74  4E 80 00 20 */	blr 