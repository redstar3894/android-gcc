/* Definitions for ELF systems with .init_array/.fini_array section
   Copyright (C) 2010
   Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "output.h"
#include "tree.h"
#include "ggc.h"

static GTY(()) section *init_array_section;
static GTY(()) section *fini_array_section;

void
elf_initfini_array_init_sections (void)
{
  init_array_section = get_unnamed_section (0, output_section_asm_op,
					    "\t.section\t.init_array");
  fini_array_section = get_unnamed_section (0, output_section_asm_op,
					    "\t.section\t.fini_array");
}

static section *
get_elf_initfini_array_priority_section (int priority,
					 bool constructor_p)
{
  section *sec;
  if (priority != DEFAULT_INIT_PRIORITY)
    {
      char buf[18];
      sprintf (buf, "%s.%.5u",
	       constructor_p ? ".init_array" : ".fini_array",
	       priority);
      sec = get_section (buf, SECTION_WRITE, NULL_TREE);
    }
  else
    sec = constructor_p ? init_array_section : fini_array_section;
  return sec;
}

/* Use .init_array section for constructors. */

void
elf_init_array_asm_out_constructor (rtx symbol, int priority)
{
  section *sec = get_elf_initfini_array_priority_section (priority,
							  true);
  assemble_addr_to_section (symbol, sec);
}

/* Use .fini_array section for destructors. */

void
elf_fini_array_asm_out_destructor (rtx symbol, int priority)
{
  section *sec = get_elf_initfini_array_priority_section (priority,
							  false);
  assemble_addr_to_section (symbol, sec);
}

#include "gt-initfini-array.h"
