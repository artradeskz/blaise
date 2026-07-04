#
# Blaise — An Object Pascal Compiler
# Copyright (c) 2026 Graeme Geldenhuys
# SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
# Licensed under the Apache License v2.0 with Runtime Library Exception.
# See LICENSE file in the project root for full license terms.
#
# Each Pascal unit is compiled directly via Blaise's unit-as-top-level
# mode (project_unit_as_toplevel, 2026-05-24): a single
# `blaise --source X.pas --output X.o` invocation runs qbe + cc -c
# + objcopy-embed in one step.  No build-driver shims, no IR-strip
# sed pipelines, no intermediate .ssa/.s files needed.
SHELL   = /bin/bash

CC      = gcc
CFLAGS  = -O2 -Wall -Wextra -std=c11

SRC_DIR     = src/main/c
PAS_SRC_DIR = src/main/pascal
ASM_DIR     = src/main/asm
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
BLAISE_FLAGS = --no-incremental

# Assembly sources — platform-specific, no C compiler needed.
ASM_OBJS = $(OBJ_DIR)/blaise_setjmp_x86_64.o \
           $(OBJ_DIR)/blaise_atomic_x86_64.o \
           $(OBJ_DIR)/blaise_utf8_x86_64.o

# Pascal RTL units compiled via the Blaise compiler.
PAS_OBJS = $(OBJ_DIR)/blaise_mem.o \
           $(OBJ_DIR)/blaise_str.o \
           $(OBJ_DIR)/blaise_set.o \
           $(OBJ_DIR)/blaise_arc.o \
           $(OBJ_DIR)/blaise_weak.o \
           $(OBJ_DIR)/blaise_float.o \
           $(OBJ_DIR)/blaise_thread.o \
           $(OBJ_DIR)/blaise_exc.o \
           $(OBJ_DIR)/rtl_platform_posix.o

OBJS = $(ASM_OBJS) $(PAS_OBJS)

.PHONY: all install clean

all: $(LIB)

$(LIB): $(OBJS)
	ar rcs $@ $^

# --- Assembly rules ---
$(OBJ_DIR)/%.o: $(ASM_DIR)/%.s
	@mkdir -p $(OBJ_DIR)
	$(CC) -c -o $@ $<

# --- Pascal unit rules (unit-as-top-level) ---
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

$(OBJ_DIR)/rtl_platform_posix.o: $(PAS_SRC_DIR)/rtl.platform.posix.pas \
                                 $(PAS_SRC_DIR)/rtl.platform.pas
	@mkdir -p $(OBJ_DIR)
	$(BLAISE) $(BLAISE_FLAGS) --source $< --unit-path $(PAS_SRC_DIR) --output $@

install: $(LIB)
	@mkdir -p $(COMPILER_BIN)
	cp $(LIB) $(COMPILER_BIN)/blaise_rtl.a
	@echo "Installed blaise_rtl.a → $(COMPILER_BIN)/blaise_rtl.a"

clean:
	rm -f $(OBJ_DIR)/*.o $(OBJ_DIR)/*.s $(OBJ_DIR)/*.ssa $(LIB)
