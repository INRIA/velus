
# Path and directory of this Makefile
# (which may be included from subdirectories)
MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MKFILE_DIR := $(patsubst %/,%,$(dir $(MKFILE_PATH)))

SRC_DIR=src

VELUSMAIN=velusmain
VELUS=velus

MAKEFILEAUTO=$(MKFILE_DIR)/Makefile.auto
MAKEFILECONFIG=$(MKFILE_DIR)/Makefile.config
COQPROJECT=$(MKFILE_DIR)/_CoqProject

ifeq ($(filter clean realclean, $(MAKECMDGOALS)),)
    ifeq ($(wildcard $(MAKEFILECONFIG)),)
    $(error Please run ./configure first)
    endif
    include $(MAKEFILECONFIG)
endif

# CompCert flags
ifeq ($(COMPCERTDIR),)
COMPCERTFLAGS=$(SILENT) -C $(MKFILE_DIR)/CompCert
else
COMPCERTFLAGS=$(SILENT) -C $(COMPCERTDIR)
endif
COMPCERT_INCLUDES=lib cfrontend backend common driver cparser debug $(ARCH)

PARSERDIR=$(SRC_DIR)/Lustre/Parser
PARSERFLAGS=$(SILENT) -C $(PARSERDIR)

TOOLSDIR=tools
AUTOMAKE=automake

EXTRACTION=extraction
EXTRACTED=$(EXTRACTION)/extracted
$(shell mkdir -p $(EXTRACTED) >/dev/null)

EXAMPLESDIR=examples
EXAMPLESFLAGS=$(SILENT) -C $(EXAMPLESDIR)
RUNEXAMPLES=$(EXAMPLESDIR)/runexamples.sh

# Menhir includes from CompCert
ifeq ($(filter clean realclean, $(MAKECMDGOALS)),)
include $(COMPCERTDIR)/Makefile.menhir
endif
export MENHIR
comma:= ,
empty:=
space:= $(empty) $(empty)
MENHIR_INCLUDES:= $(subst $(space),$(comma),$(MENHIR_INCLUDES))

# ocamlbuild flags
VERBOSITY=-verbose 1
FLAGS=-Is $(SRC_DIR),$(EXTRACTED) -use-ocamlfind -use-menhir \
      -pkgs str,unix,menhirLib -no-hygiene $(VERBOSITY)
	#-cflags $(MENHIR_INCLUDES)$(WARNINGS)
TARGET=native
BUILDDIR=_build

# flag to prevent coqc from taking CompCert directories into account (see Makefile.auto)
export OTHERFLAGS=-exclude-dir CompCert -w -extraction

bold=$(shell tput bold)
blue=$(shell tput setaf 4)
red=$(shell tput setaf 9)
green=$(shell tput setaf 10)
normal=$(shell tput sgr0)

ifndef VERBOSE
SILENT=-s
#WARNINGS=,-w,-3-20
WARNINGS=
VERBOSITY=
.SILENT:
endif
