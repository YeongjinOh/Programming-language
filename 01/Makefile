DFILES = D.v
PFILES = $(shell find P??.v)
EFILES = $(shell find E??.v)

POFILES = $(patsubst %.v,%.vo,$(PFILES))
EOFILES = $(patsubst %.v,%.vo,$(EFILES))

all: $(DFILES) $(PFILES) Makefile.coq
	$(MAKE) -f Makefile.coq $(POFILES)

eval: $(DFILES) $(PFILES) $(EFILES) Makefile.coq
	$(MAKE) -f Makefile.coq $(EOFILES)
	bash ./check.sh

submission: eval
	zip submission.zip P??.v

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm _CoqProject Makefile.coq

Makefile.coq: Makefile $(PFILES) $(EFILES)
	(echo $(DFILES) $(PFILES) $(EFILES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
