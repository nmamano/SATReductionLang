######################################
###### SAT solver configuration ######
######################################

MINISATDIR = satsolvers/minisat-2.2.0/core
export LIB = minisat
export MROOT = ..

PICOSATDIR = satsolvers/picosat-957

#Choose between MINISAT and PICOSAT
ifndef SATSOLVER
SATSOLVER = MINISAT
endif

######################################
####### Generic configuration ########
######################################

CXX    ?= g++
CFLAGS ?= -O3 -Wall
CFLAGS  += -std=c++0x
LFLAGS ?= -Wall

all : juezejecutable

htmls :

pdfs :

clean :

distclean :
	rm -f juezejecutable *.o
	test -d $(MINISATDIR) && rm -f $(MINISATDIR)/libminisat_release.a && $(MAKE) -C $(MINISATDIR) clean || echo "...no MiniSat..."
	test -d $(PICOSATDIR) && rm -f $(PICOSATDIR)/libpicosat.a && cd $(PICOSATDIR) && ./configure && $(MAKE) clean || echo "...no PicoSat..."

######################################
####### Program build rules ##########
######################################

%.o : %.cc
	$(CXX) $(CFLAGS) -c -o $@ $<

ifeq ($(SATSOLVER),MINISAT)
CFLAGS += -Wno-parentheses -I$(MINISATDIR)/$(MROOT) -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -D USE_MINISAT
LFLAGS += -L$(MINISATDIR) -lminisat_release

juezejecutable : lenguajereduccionesnp.o $(MINISATDIR)/libminisat_release.a
	$(CXX) $(filter-out %.a, $^) $(LFLAGS) -o $@

$(MINISATDIR)/libminisat_release.a :
	$(MAKE) -C $(MINISATDIR) libminisat_release.a
else ifeq ($(SATSOLVER),PICOSAT)
CFLAGS += -I$(PICOSATDIR) -D USE_PICOSAT
LFLAGS += -L$(PICOSATDIR) -lpicosat

juezejecutable : lenguajereduccionesnp.o $(PICOSATDIR)/libpicosat.a
	$(CXX) $(filter-out %.a, $^) $(LFLAGS) -o $@

$(PICOSATDIR)/libpicosat.a :
	cd $(PICOSATDIR) && ./configure && $(MAKE) libpicosat.a
endif

.PHONY : $(MINISATDIR)/libminisat_release.a $(PICOSATDIR)/libpicosat.a htmls pdfs clean distclean hashes check
