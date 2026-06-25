#
# Blaise — An Object Pascal Compiler
# Copyright (c) 2026 Graeme Geldenhuys
# SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
# Licensed under the Apache License v2.0 with Runtime Library Exception.
# See LICENSE file in the project root for full license terms.
#
# Each RTL unit is compiled directly via Blaise's unit-as-top-level mode: a
# single `blaise --source X.pas --output X.o` invocation produces the object.
# The RTL is now entirely pure Pascal (the four hand-written *_x86_64.s files
# were migrated to inline-asm `.pas` units), so the whole archive builds through
# Blaise's own internal assembler — no external assembler, no gcc, no .s files.
SHELL   = /bin/bash

PAS_SRC_DIR = src/main/pascal
OBJ_DIR     = target
LIB         = $(OBJ_DIR)/blaise_rtl.a

# Where the compiler binary lives — install copies the RTL there so the
# driver finds it automatically next to itself.
COMPILER_BIN = ../compiler/target
BLAISE       = $(COMPILER_BIN)/blaise
# This Makefile IS a hand-managed separate-compilation system: it compiles each
# RTL unit to its own object and archives an explicit object list.  The
# compiler's own incremental mode (now the default) would, on top of that, write
# per-dependency side-effect .o files next to each output and skip inlining a
# used unit's bodies — but those side-effect objects are not in the archive's
# object list, so a cross-unit symbol (e.g. typeinfo_TRtlPlatform, referenced by
# the derived TRtlPlatformPosix in another unit) ends up undefined at link.
# Force whole-program compilation per unit so every unit object is self-contained.
#
# --assembler internal: assemble each unit to its .o with Blaise's own in-process
# assembler instead of `cc -c`, so building the RTL needs no external assembler.
BLAISE_FLAGS = --no-incremental --assembler internal

# Every RTL unit is now pure Pascal (the four hand-written *_x86_64.s files —
# start, setjmp, atomic, utf8 — were migrated to inline-asm `.pas` units).  The
# RTL therefore builds entirely through Blaise's own pipeline: no $(CC), no
# external assembler, no .s files.
PAS_OBJS = $(OBJ_DIR)/blaise_start.o \
           $(OBJ_DIR)/blaise_atomic.o \
           $(OBJ_DIR)/blaise_setjmp.o \
           $(OBJ_DIR)/blaise_utf8.o \
           $(OBJ_DIR)/blaise_mem.o \
           $(OBJ_DIR)/blaise_str.o \
           $(OBJ_DIR)/blaise_set.o \
           $(OBJ_DIR)/blaise_arc.o \
           $(OBJ_DIR)/blaise_weak.o \
           $(OBJ_DIR)/blaise_float.o \
           $(OBJ_DIR)/blaise_thread.o \
           $(OBJ_DIR)/blaise_exc.o \
           $(OBJ_DIR)/rtl_platform_layout_linux.o \
           $(OBJ_DIR)/rtl_platform_posix.o

OBJS = $(PAS_OBJS)

.PHONY: all install clean

all: $(LIB)

$(LIB): $(OBJS)
	ar rcs $@ $^

# --- Pascal unit rules (unit-as-top-level) ---
$(OBJ_DIR)/blaise_utf8.o: $(PAS_SRC_DIR)/blaise_utf8.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_start.o: $(PAS_SRC_DIR)/blaise_start.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_atomic.o: $(PAS_SRC_DIR)/blaise_atomic.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_setjmp.o: $(PAS_SRC_DIR)/blaise_setjmp.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_mem.o: $(PAS_SRC_DIR)/blaise_mem.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_str.o: $(PAS_SRC_DIR)/blaise_str.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_set.o: $(PAS_SRC_DIR)/blaise_set.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_arc.o: $(PAS_SRC_DIR)/blaise_arc.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_weak.o: $(PAS_SRC_DIR)/blaise_weak.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_float.o: $(PAS_SRC_DIR)/blaise_float.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_thread.o: $(PAS_SRC_DIR)/blaise_thread.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/blaise_exc.o: $(PAS_SRC_DIR)/blaise_exc.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/rtl_platform_layout_linux.o: $(PAS_SRC_DIR)/rtl.platform.layout.linux.pas \
                                 $(PAS_SRC_DIR)/rtl.platform.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

$(OBJ_DIR)/rtl_platform_posix.o: $(PAS_SRC_DIR)/rtl.platform.posix.pas \
                                 $(PAS_SRC_DIR)/rtl.platform.layout.linux.pas \
                                 $(PAS_SRC_DIR)/rtl.platform.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

install: $(LIB)
	@mkdir -p $(COMPILER_BIN)
	cp $(LIB) $(COMPILER_BIN)/blaise_rtl.a
	@echo "Installed blaise_rtl.a → $(COMPILER_BIN)/blaise_rtl.a"

clean:
	rm -f $(OBJ_DIR)/*.o $(OBJ_DIR)/*.s $(OBJ_DIR)/*.ssa $(LIB)
