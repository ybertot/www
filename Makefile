
### Coq website : generation of static pages ###

DST:=dest
YAMLPP:=yamlpp-0.3/yamlpp.ml
PP=mkdir -p $(dir $@) && ocaml $(YAMLPP) $< -o $@
INCLS:=incl/header.html incl/footer.html
DEPS:=$(INCLS) $(YAMLPP)

all: html aliases news newsaliases

clean:
	rm -rf $(DST)/*

$(YAMLPP): $(YAMLPP:.ml=.mll)
	ocamllex $<

.PHONY: all html aliases news newsaliases clean

## Generated pages : their list and how to generate them

PAGES:= \
 $(patsubst %,$(DST)/%/index.html, \
   welcome \
   download \
   documentation \
   community \
   a-short-introduction-to-coq \
   tutorial \
   tutorial/0-getting-started \
   tutorial/1-basic-predicate-calculus \
   tutorial/2-induction \
   tutorial/3-modules \
   faq \
   related-tools \
   about-coq \
   coqide-screenshots \
   adt \
   adt-english \
   adt/demarrage \
   adt/biblios \
   adt/automatisation \
   adt/tactiques \
   adt/egalite-terminaison \
   adt/interfaces \
   coq-workshop \
   coq-workshop/2009 \
   coq-workshop/2009/accepted-papers \
   coq-workshop/2009/program \
   the-coq-workshop-old \
   coq-workshop/2010/cfp \
   coq-workshop/2010 \
   coq-workshop/2012 \
   coq-workshop/2013 \
   macos-plugin-note \
   coq-82-beta \
   coq-82-beta-detailed-description \
   coq-82-rc \
   coq-82 \
   v84 \
   v84-0 \
   coq-84 \
   coq-8.4 \
   coq-83 \
   coq-working-group-february-14th-2013 \
   wgs \
   who-did-what-in-coq \
   who-did-what-in-coq-8.2 \
   who-did-what-in-coq-8.3 \
   who-did-what-in-coq-8.4 \
   tutorial-nahas )

html: $(PAGES)

# NOTA: instead of having commands on separate lines (starting by tabs)
# we use here the shorter syntax "target: dep; action"

$(DST)/welcome/index.html: pages/1.html $(DEPS) ; $(PP)
$(DST)/download/index.html: pages/3.html $(DEPS) ; $(PP)
$(DST)/documentation/index.html: pages/4.html $(DEPS) ; $(PP)
$(DST)/community/index.html: pages/5.html $(DEPS); $(PP)
$(DST)/a-short-introduction-to-coq/index.html: pages/6.html $(DEPS); $(PP)
$(DST)/tutorial/index.html: pages/7.html $(DEPS); $(PP)
$(DST)/tutorial/0-getting-started/index.html: pages/8.html $(DEPS); $(PP)
$(DST)/tutorial/1-basic-predicate-calculus/index.html: pages/9.html $(DEPS); $(PP)
$(DST)/tutorial/2-induction/index.html: pages/10.html $(DEPS); $(PP)
$(DST)/tutorial/3-modules/index.html: pages/11.html $(DEPS); $(PP)
$(DST)/faq/index.html: pages/16.html $(DEPS); $(PP)
$(DST)/related-tools/index.html: pages/17.html $(DEPS); $(PP)
$(DST)/about-coq/index.html: pages/19.html $(DEPS); $(PP)
$(DST)/coqide-screenshots/index.html: pages/57.html $(DEPS); $(PP)
$(DST)/coq-82-beta/index.html: pages/60.html $(DEPS); $(PP)
$(DST)/coq-82-beta-detailed-description/index.html: pages/61.html $(DEPS); $(PP)
$(DST)/adt/index.html: pages/63.html $(DEPS); $(PP)
$(DST)/adt-english/index.html: pages/64.html $(DEPS); $(PP)
$(DST)/coq-82-rc/index.html: pages/66.html $(DEPS); $(PP)
$(DST)/coq-82/index.html: pages/73.html $(DEPS); $(PP)
$(DST)/adt/demarrage/index.html: pages/74.html $(DEPS); $(PP)
$(DST)/adt/biblios/index.html: pages/75.html $(DEPS); $(PP)
$(DST)/adt/automatisation/index.html: pages/76.html $(DEPS); $(PP)
$(DST)/coq-workshop/2009/index.html: pages/77.html $(DEPS); $(PP)
$(DST)/adt/tactiques/index.html: pages/79.html $(DEPS); $(PP)
$(DST)/coq-workshop/2009/accepted-papers/index.html: pages/80.html $(DEPS); $(PP)
$(DST)/coq-workshop/2009/program/index.html: pages/82.html $(DEPS); $(PP)
$(DST)/the-coq-workshop-old/index.html: pages/84.html $(DEPS); $(PP)
$(DST)/coq-workshop/2010/cfp/index.html: pages/86.html $(DEPS); $(PP)
$(DST)/coq-workshop/2010/index.html: pages/87.html $(DEPS); $(PP)
$(DST)/coq-workshop/index.html: pages/88.html $(DEPS); $(PP)
$(DST)/adt/egalite-terminaison/index.html: pages/89.html $(DEPS); $(PP)
$(DST)/macos-plugin-note/index.html: pages/90.html $(DEPS); $(PP)
$(DST)/who-did-what-in-coq/index.html: pages/92.html $(DEPS); $(PP)
$(DST)/adt/interfaces/index.html: pages/97.html $(DEPS); $(PP)
$(DST)/coq-workshop/2012/index.html: pages/101.html $(DEPS); $(PP)
$(DST)/v84/index.html: pages/102.html $(DEPS); $(PP)
$(DST)/v84-0/index.html: pages/103.html $(DEPS); $(PP)
$(DST)/coq-84/index.html: pages/104.html $(DEPS); $(PP)
$(DST)/coq-8.4/index.html: pages/108.html $(DEPS); $(PP)
$(DST)/coq-83/index.html: pages/109.html $(DEPS); $(PP)
$(DST)/coq-workshop/2013/index.html: pages/111.html $(DEPS); $(PP)
$(DST)/coq-working-group-february-14th-2013/index.html: pages/112.html $(DEPS); $(PP)
$(DST)/wgs/index.html: pages/113.html $(DEPS); $(PP)
$(DST)/who-did-what-in-coq-8.2/index.html: pages/116.html $(DEPS); $(PP)
$(DST)/who-did-what-in-coq-8.3/index.html: pages/117.html $(DEPS); $(PP)
$(DST)/who-did-what-in-coq-8.4/index.html: pages/118.html $(DEPS); $(PP)
$(DST)/tutorial-nahas/index.html: pages/123.html $(DEPS); $(PP)

## Aliases. Handled here via symbolink links, could also be Apache redirects

ALIASES:= \
 $(addprefix $(DST)/, \
   index.html \
   files \
   styles \
   getting-started \
   1-basic-predicate-calculus \
   what-is-coq \
   coq-workshop/2009/cfp \
   the-coq-workshop \
   the-coq-workshop-2009-0 \
   the-coq-workshop-2010 \
   the-coq-workshop-2010-0 \
   the-coq-workshop-2012 \
   the-coq-workshop-2013 \
   adt-coq \
   journée-de-démarrage-de-ladt \
   journée-«-bibliothèques-» \
   journée-«-bibliothèques-»-du-11-décembre-2008 \
   journée-«-automatisation-»-du-24-mars-2009 \
   journée-«-tactiques-»-du-30-juin-2009 \
   journée-«-égalité-et-terminaison-»-du-2-février-2010 \
   journée-«-interfaces-»-du-27-octobre-2010 \
   coq-82-detailed-description \
   coq-84-0 \
   coq-8.3 )

aliases: $(ALIASES)

$(DST)/index.html: ; ln -s welcome/index.html $@

$(DST)/files: ; ln -snf ../files $@
$(DST)/styles: ; ln -snf ../styles $@
$(DST)/coq-workshop/files: ; mkdir -p $(dir $@) && ln -snf ../files $@

$(DST)/getting-started: ; ln -snf tutorial/0-getting-started $@
$(DST)/1-basic-predicate-calculus: ; ln -snf tutorial/1-basic-predicate-calculus $@
$(DST)/what-is-coq: ; ln -snf about-coq $@
$(DST)/coq-workshop/2009/cfp: ; mkdir -p $(dir $@) && ln -snf ../../news/69.html $@
$(DST)/the-coq-workshop: ; ln -snf coq-workshop $@
$(DST)/the-coq-workshop-2009-0: ; ln -snf coq-workshop/2009 $@
$(DST)/the-coq-workshop-2010: ; ln -snf coq-workshop/2010 $@
$(DST)/the-coq-workshop-2010-0: ; ln -snf coq-workshop/2010 $@
$(DST)/the-coq-workshop-2012: ; ln -snf coq-workshop/2012 $@
$(DST)/the-coq-workshop-2013: ; ln -snf coq-workshop/2013 $@
$(DST)/adt-coq: ; ln -snf adt $@
$(DST)/journée-de-démarrage-de-ladt: ; ln -snf adt/demarrage $@
$(DST)/journée-«-bibliothèques-»: ; ln -snf adt/biblios $@
$(DST)/journée-«-bibliothèques-»-du-11-décembre-2008: ; ln -snf adt/biblios $@
$(DST)/journée-«-automatisation-»-du-24-mars-2009: ; ln -snf adt/automatisation $@
$(DST)/journée-«-tactiques-»-du-30-juin-2009: ; ln -snf adt/tactiques $@ 
$(DST)/journée-«-égalité-et-terminaison-»-du-2-février-2010: ; ln -snf adt/egalite-terminaison $@
$(DST)/journée-«-interfaces-»-du-27-octobre-2010: ; ln -snf adt/interfaces $@
$(DST)/coq-82-detailed-description: ; ln -snf coq-82 $@
$(DST)/coq-84-0: ; ln -snf coq-8.4 $@
$(DST)/coq-8.3: ; ln -snf coq-83 $@

## News

NEWS:= \
  122 121 120 119 115 114 110 107 106 105 100 99 98 96 95 \
  94 93 91 83 81 78 72 71 70 69 68 67 65 62 59 58 20

RECENTNEWS:= 122

NEWSSRC:=$(addprefix news/,$(NEWS))
NEWSDST:=$(patsubst %,$(DST)/news/%.html,$(NEWS))

news: $(DST)/news/index.html $(DST)/rss.xml $(NEWSDST)

$(DST)/news/index.html: $(NEWSSRC) $(DEPS) incl/news/item.html
	mkdir -p $(dir $@)
	ocaml $(YAMLPP) incl/header.html $(patsubst %,% incl/news/item.html,$(NEWSSRC)) incl/footer.html -o $@

$(DST)/news/%.html: news/% $(DEPS) incl/news/solo.html
	mkdir -p $(dir $@)
	ocaml $(YAMLPP) $< incl/news/solo.html -o $@

$(DST)/rss.xml: $(NEWSSRC) incl/rss/header.xml incl/rss/footer.xml incl/rss/item.xml $(YAMLPP)
	ocaml $(YAMLPP) incl/rss/header.xml $(patsubst %,% incl/rss/item.xml,$(NEWSSRC)) incl/rss/footer.xml -o $@

NEWSALIASES:= \
 $(patsubst %,$(DST)/news/%/index.html, \
   the-coq-workshop-2009 \
   announcing-lngen \
   a-locally-nameless-backend-for-ott \
   first-asian-pacific-coq-summer-school \
   a-tactic-for-deciding-kleene-algebras \
   coq-82pl1-is-out \
   announcing-ssreflect-version-12 \
   coq-83-beta-version \
   coq-workshop-2010 \
   2nd-asian-pacific-coq-summer-school \
   alpha-release-of-coq-modulo-theories \
   coq-83-is-out \
   coq-83pl2-is-out \
   3rd-asian-pacific-summer-school-on-formal-methods \
   coq-workshop-2011 \
   coq-83pl3-is-out \
   beta-release-of-coq-84 \
   release-candidate-of-coq-84-is-out \
   coq-84-is-out \
   coq-received-acm-sigplan-programming-languages-software-2013-award \
   coq-source-repository-migrated-to-git \
   coq-received-acm-software-system-2013-award \
   coq-84pl4-is-out \
   coq-is-hiring-a-specialized-engineer-for-2-years )

newsaliases: $(NEWSALIASES)

$(DST)/news/the-coq-workshop-2009/index.html: ; mkdir -p $(dir $@) && ln -s ../69.html $@
$(DST)/news/announcing-lngen/index.html: ; mkdir -p $(dir $@) && ln -s ../70.html $@
$(DST)/news/a-locally-nameless-backend-for-ott/index.html: ; mkdir -p $(dir $@) && ln -s ../71.html $@
$(DST)/news/first-asian-pacific-coq-summer-school/index.html: ; mkdir -p $(dir $@) && ln -s ../72.html $@
$(DST)/news/a-tactic-for-deciding-kleene-algebras/index.html: ; mkdir -p $(dir $@) && ln -s ../78.html $@
$(DST)/news/coq-82pl1-is-out/index.html: ; mkdir -p $(dir $@) && ln -s ../81.html $@
$(DST)/news/announcing-ssreflect-version-12/index.html: ; mkdir -p $(dir $@) && ln -s ../83.html $@
$(DST)/news/coq-83-beta-version/index.html: ; mkdir -p $(dir $@) && ln -s ../91.html $@
$(DST)/news/coq-workshop-2010/index.html: ; mkdir -p $(dir $@) && ln -s ../93.html $@
$(DST)/news/2nd-asian-pacific-coq-summer-school/index.html: ; mkdir -p $(dir $@) && ln -s ../94.html $@
$(DST)/news/alpha-release-of-coq-modulo-theories/index.html: ; mkdir -p $(dir $@) && ln -s ../95.html $@
$(DST)/news/coq-83-is-out/index.html: ; mkdir -p $(dir $@) && ln -s ../96.html $@
$(DST)/news/coq-83pl2-is-out/index.html: ; mkdir -p $(dir $@) && ln -s ../98.html $@
$(DST)/news/3rd-asian-pacific-summer-school-on-formal-methods/index.html: ; mkdir -p $(dir $@) && ln -s ../99.html $@
$(DST)/news/coq-workshop-2011/index.html: ; mkdir -p $(dir $@) && ln -s ../100.html $@
$(DST)/news/coq-83pl3-is-out/index.html: ; mkdir -p $(dir $@) && ln -s ../105.html $@
$(DST)/news/beta-release-of-coq-84/index.html: ; mkdir -p $(dir $@) && ln -s ../106.html $@
$(DST)/news/release-candidate-of-coq-84-is-out/index.html: ; mkdir -p $(dir $@) && ln -s ../107.html $@
$(DST)/news/coq-84-is-out/index.html: ; mkdir -p $(dir $@) && ln -s ../110.html $@
$(DST)/news/coq-received-acm-sigplan-programming-languages-software-2013-award/index.html: ; mkdir -p $(dir $@) && ln -s ../114.html $@
$(DST)/news/coq-source-repository-migrated-to-git/index.html: ; mkdir -p $(dir $@) && ln -s ../115.html $@
$(DST)/news/coq-received-acm-software-system-2013-award/index.html: ; mkdir -p $(dir $@) && ln -s ../119.html $@
$(DST)/news/coq-84pl4-is-out/index.html: ; mkdir -p $(dir $@) && ln -s ../120.html $@
$(DST)/news/coq-is-hiring-a-specialized-engineer-for-2-years/index.html: ; mkdir -p $(dir $@) && ln -s ../121.html $@

printenv:
	@echo "### PAGES ###"
	@echo $(PAGES) | tr " " "\n"
	@echo "### ALIASES ###"
	@echo $(ALIASES) | tr " " "\n"

# Needs python 2.x (this exists also for python 3, with a different syntax)
run:
	@echo "Starting a local web server for test"
	@echo "It is accessible at: http://localhost:8000"
	cd $(DST) && python -m SimpleHTTPServer 8000