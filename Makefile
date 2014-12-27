
### Coq website : generation of static pages ###

DST:=dest
YAMLPP:=yamlpp-0.3/yamlpp.ml
INCLS:=incl/header.html incl/footer.html incl/news/recent.html
DEPS:=$(INCLS) $(YAMLPP)

all: html aliases news newsaliases

clean:
	rm -rf $(DST)/*

$(YAMLPP): $(YAMLPP:.ml=.mll)
	ocamllex $<

.PHONY: all html aliases news newsaliases clean

## Generated pages : their list and how to generate them

PAGES:= \
 1 3 4 5 6 7 8 9 10 11 16 17 19 57 60 61 63 64 66 \
 73 74 75 76 77 79 80 82 84 86 87 88 89 90 92 97 \
 101 102 103 104 108 109 111 112 113 116 117 118 123

html: $(patsubst %,$(DST)/node/%.html, $(PAGES))

$(DST)/node/%: pages/% $(DEPS)
	mkdir -p $(dir $@) && ocaml $(YAMLPP) $< -o $@

## Aliases. Handled here via symbolink links, could also be Apache redirects

ALIASES:= \
 $(DST)/index.html \
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
   tutorial-nahas \
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

aliases: $(ALIASES) $(DST)/styles $(DST)/files $(DST)/coq-workshop/files

# NOTA: instead of having commands on separate lines (starting by tabs)
# we use here the shorter syntax "target: dep; action"

LINK= mkdir -p $(dir $@) && ln -s

$(DST)/index.html: ; $(LINK) node/1.html $@
$(DST)/welcome/index.html: ; $(LINK) ../node/1.html $@
$(DST)/download/index.html: ; $(LINK) ../node/3.html $@
$(DST)/documentation/index.html: ; $(LINK) ../node/4.html $@
$(DST)/community/index.html: ; $(LINK) ../node/5.html $@
$(DST)/a-short-introduction-to-coq/index.html: ; $(LINK) ../node/6.html $@
$(DST)/tutorial/index.html: ; $(LINK) ../node/7.html $@
$(DST)/tutorial/0-getting-started/index.html: ; $(LINK) ../../node/8.html $@
$(DST)/tutorial/1-basic-predicate-calculus/index.html: ; $(LINK) ../../node/9.html $@
$(DST)/tutorial/2-induction/index.html: ; $(LINK) ../../node/10.html $@
$(DST)/tutorial/3-modules/index.html: ; $(LINK) ../../node/11.html $@
$(DST)/faq/index.html: ; $(LINK) ../node/16.html $@
$(DST)/related-tools/index.html: ; $(LINK) ../node/17.html $@
$(DST)/about-coq/index.html: ; $(LINK) ../node/19.html $@
$(DST)/coqide-screenshots/index.html: ; $(LINK) ../node/57.html $@
$(DST)/coq-82-beta/index.html: ; $(LINK) ../node/60.html $@
$(DST)/coq-82-beta-detailed-description/index.html: ; $(LINK) ../node/61.html $@
$(DST)/adt/index.html: ; $(LINK) ../node/63.html $@
$(DST)/adt-english/index.html: ; $(LINK) ../node/64.html $@
$(DST)/coq-82-rc/index.html: ; $(LINK) ../node/66.html $@
$(DST)/coq-82/index.html: ; $(LINK) ../node/73.html $@
$(DST)/adt/demarrage/index.html: ; $(LINK) ../../node/74.html $@
$(DST)/adt/biblios/index.html: ; $(LINK) ../../node/75.html $@
$(DST)/adt/automatisation/index.html: ; $(LINK) ../../node/76.html $@
$(DST)/coq-workshop/2009/index.html: ; $(LINK) ../../node/77.html $@
$(DST)/adt/tactiques/index.html: ; $(LINK) ../../node/79.html $@
$(DST)/coq-workshop/2009/accepted-papers/index.html: ; $(LINK) ../../../node/80.html $@
$(DST)/coq-workshop/2009/program/index.html: ; $(LINK) ../../../node/82.html $@
$(DST)/the-coq-workshop-old/index.html: ; $(LINK) ../node/84.html $@
$(DST)/coq-workshop/2010/cfp/index.html: ; $(LINK) ../../../node/86.html $@
$(DST)/coq-workshop/2010/index.html: ; $(LINK) ../../node/87.html $@
$(DST)/coq-workshop/index.html: ; $(LINK) ../node/88.html $@
$(DST)/adt/egalite-terminaison/index.html: ; $(LINK) ../../node/89.html $@
$(DST)/macos-plugin-note/index.html: ; $(LINK) ../node/90.html $@
$(DST)/who-did-what-in-coq/index.html: ; $(LINK) ../node/92.html $@
$(DST)/adt/interfaces/index.html: ; $(LINK) ../../node/97.html $@
$(DST)/coq-workshop/2012/index.html: ; $(LINK) ../../node/101.html $@
$(DST)/v84/index.html: ; $(LINK) ../node/102.html $@
$(DST)/v84-0/index.html: ; $(LINK) ../node/103.html $@
$(DST)/coq-84/index.html: ; $(LINK) ../node/104.html $@
$(DST)/coq-8.4/index.html: ; $(LINK) ../node/108.html $@
$(DST)/coq-83/index.html: ; $(LINK) ../node/109.html $@
$(DST)/coq-workshop/2013/index.html: ; $(LINK) ../../node/111.html $@
$(DST)/coq-working-group-february-14th-2013/index.html: ; $(LINK) ../node/112.html $@
$(DST)/wgs/index.html: ; $(LINK) ../node/113.html $@
$(DST)/who-did-what-in-coq-8.2/index.html: ; $(LINK) ../node/116.html $@
$(DST)/who-did-what-in-coq-8.3/index.html: ; $(LINK) ../node/117.html $@
$(DST)/who-did-what-in-coq-8.4/index.html: ; $(LINK) ../node/118.html $@
$(DST)/tutorial-nahas/index.html: ; $(LINK) ../node/123.html $@

$(DST)/files: ; ln -snf ../files $@
$(DST)/styles: ; ln -snf ../styles $@
$(DST)/coq-workshop/files: ; mkdir -p $(dir $@) && ln -snf ../files $@

# Alternative / compatibility aliases

$(DST)/getting-started/index.html: ; $(LINK) ../node/8.html $@
$(DST)/1-basic-predicate-calculus/index.html: ; $(LINK) ../node/9.html $@
$(DST)/what-is-coq/index.html: ; $(LINK) ../node/19.html $@
$(DST)/coq-workshop/2009/cfp/index.html: ; $(LINK) ../../../news/69.html $@
$(DST)/the-coq-workshop/index.html: ; $(LINK) ../coq-workshop/index.html $@
$(DST)/the-coq-workshop-2009-0/index.html: ; $(LINK) ../coq-workshop/2009/index.html $@
$(DST)/the-coq-workshop-2010/index.html: ; $(LINK) ../coq-workshop/2010/index.html $@
$(DST)/the-coq-workshop-2010-0/index.html: ; $(LINK) ../coq-workshop/2010/index.html $@
$(DST)/the-coq-workshop-2012/index.html: ; $(LINK) ../coq-workshop/2012/index.html $@
$(DST)/the-coq-workshop-2013/index.html: ; $(LINK) ../coq-workshop/2013/index.html $@
$(DST)/adt-coq/index.html: ; $(LINK) ../adt/index.html $@
$(DST)/journée-de-démarrage-de-ladt/index.html: ; $(LINK) ../adt/demarrage/index.html $@
$(DST)/journée-«-bibliothèques-»/index.html: ; $(LINK) ../adt/biblios/index.html $@
$(DST)/journée-«-bibliothèques-»-du-11-décembre-2008/index.html: ; $(LINK) ../adt/biblios/index.html $@
$(DST)/journée-«-automatisation-»-du-24-mars-2009/index.html: ; $(LINK) ../adt/automatisation/index.html $@
$(DST)/journée-«-tactiques-»-du-30-juin-2009/index.html: ; $(LINK) ../adt/tactiques/index.html $@
$(DST)/journée-«-égalité-et-terminaison-»-du-2-février-2010/index.html: ; $(LINK) ../adt/egalite-terminaison/index.html $@
$(DST)/journée-«-interfaces-»-du-27-octobre-2010/index.html: ; $(LINK) ../adt/interfaces/index.html $@
$(DST)/coq-82-detailed-description/index.html: ; $(LINK) ../coq-82/index.html $@
$(DST)/coq-84-0/index.html: ; $(LINK) ../coq-8.4/index.html $@
$(DST)/coq-8.3/index.html: ; $(LINK) ../coq-83/index.html $@

## News

NEWS:= \
  122 121 120 119 115 114 110 107 106 105 100 99 98 96 95 \
  94 93 91 83 81 78 72 71 70 69 68 67 65 62 59 58 20

RECENTNEWS:= 122

NEWSSRC:=$(addprefix news/,$(NEWS))
NEWSDST:=$(patsubst %,$(DST)/news/%.html,$(NEWS))

news: $(DST)/news/index.html $(DST)/rss.xml $(NEWSDST)

incl/news/recent.html: $(YAMLPP) $(addprefix news/,$(RECENTNEWS))
	ocaml $(YAMLPP) -o $@ $(patsubst %,news/% incl/news/li.html,$(RECENTNEWS))

$(DST)/news/index.html: $(NEWSSRC) $(DEPS) incl/news/item.html incl/news/title.html
	mkdir -p $(dir $@)
	ocaml $(YAMLPP) -o $@ \
          incl/news/title.html \
          incl/header.html \
          $(patsubst %,% incl/news/item.html,$(NEWSSRC)) \
          incl/footer.html

$(DST)/news/%.html: news/% $(DEPS) incl/news/solo.html
	mkdir -p $(dir $@)
	ocaml $(YAMLPP) $< incl/news/solo.html -o $@

$(DST)/rss.xml: $(NEWSSRC) incl/rss/header.xml incl/rss/footer.xml incl/rss/item.xml $(YAMLPP)
	ocaml $(YAMLPP) -o $@ \
          incl/rss/header.xml \
          $(patsubst %,% incl/rss/item.xml,$(NEWSSRC)) \
          incl/rss/footer.xml

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