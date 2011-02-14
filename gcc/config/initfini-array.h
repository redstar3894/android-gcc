/* Definitions for ELF systems with .init_array/.fini_array section
   support.
   Copyright (C) 2010
   Free Software Foundation, Inc.

   This file is part of GCC.

   GCC is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published
   by the Free Software Foundation; either version 3, or (at your
   option) any later version.

   GCC is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
   or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
   License for more details.

   You should have received a copy of the GNU General Public License
   along with GCC; see the file COPYING3.  If not see
   <http://www.gnu.org/licenses/>.  */

/* No need for .ctors/.dtors section since linker can place them in
   .init_array/.fini_array section.  */
#define NO_CTORS_DTORS_SECTIONS

#undef INIT_SECTION_ASM_OP
#undef FINI_SECTION_ASM_OP

/* FIXME: INIT_ARRAY_SECTION_ASM_OP and FINI_ARRAY_SECTION_ASM_OP
	  aren't used in any assembly codes.  But we have to define
	  them to something.  */
#define INIT_ARRAY_SECTION_ASM_OP Something
#define FINI_ARRAY_SECTION_ASM_OP Something

#ifndef TARGET_ASM_INIT_SECTIONS
#define TARGET_ASM_INIT_SECTIONS elf_initfini_array_init_sections
#endif
extern void elf_initfini_array_init_sections (void);

/* Use .init_array/.fini_array section for constructors and destructors. */
#undef TARGET_ASM_CONSTRUCTOR
#define TARGET_ASM_CONSTRUCTOR elf_init_array_asm_out_constructor
#undef TARGET_ASM_DESTRUCTOR
#define TARGET_ASM_DESTRUCTOR elf_fini_array_asm_out_destructor
extern void elf_init_array_asm_out_constructor (rtx, int);
extern void elf_fini_array_asm_out_destructor (rtx, int);
