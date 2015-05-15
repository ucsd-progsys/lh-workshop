RSYNC=$(shell pwd)/sync.sh
remoteuser=rjhala
remotedir=/home/rjhala/public_html/liquid/book
remotehost=goto.ucsd.edu

LIQUIDCLIENT=../liquid-client
SLIDES=dist/_slides
SITE=dist/_site
DIST=dist/_build
TEMPLATES=assets/templates
FILTERS=assets/filters

##############################################

INDEXER=$(FILTERS)/Toc.hs
METATEMPLATE=$(TEMPLATES)/pagemeta.template
INDEXTEMPLATE=$(TEMPLATES)/index.template
PREAMBLE=$(TEMPLATES)/preamble.lhs
BIB=$(TEMPLATES)/bib.lhs

# generated
PAGETEMPLATE=$(DIST)/page.template
LINKS=$(DIST)/links.txt
INDEX=$(DIST)/index.lhs

##############################################

PANDOCPDF=pandoc \
	--highlight-style=tango \
	--from=markdown+lhs \
	--biblio templates/sw.bib \
	--chapters \
	--latex-engine=pdflatex \
	--template=templates/default.latex \
	--filter $(FILTERS)/Figures.hs \
	--filter $(FILTERS)/Latex.hs

PANDOCHTML=pandoc \
     --from=markdown+lhs \
	 --to=html5 \
     -s --mathjax \
	 --standalone \
     --parse-raw \
	 --mathjax \
	 --toc \
	 --section-divs \
	 --filter $(LIQUIDCLIENT)/templates/codeblock.hs \
	 --filter $(FILTERS)/Figures.hs \
	 --filter $(FILTERS)/Html.hs \
	 --variable=notitle \
	 --highlight-style=tango

####################################################################

lhsObjects  := $(wildcard src/*.lhs)
texObjects  := $(patsubst %.lhs,%.tex,$(wildcard src/*.lhs))
htmlObjects := $(patsubst %.lhs,%.html,$(wildcard src/*.lhs))

####################################################################

all: pdf

pdf: $(lhsObjects)
	cat $(lhsObjects) > $(DIST)/pbook.lhs
	PANDOC_TARGET=pbook.pdf $(PANDOCPDF) $(PREAMBLE) $(BIB) $(DIST)/pbook.lhs -o $(DIST)/pbook.pdf

html: indexhtml $(htmlObjects)
	mv src/*.html               $(SITE)/
	cp -r assets/img            $(SITE)/
	cp -r $(LIQUIDCLIENT)/fonts $(SITE)/
	cp -r $(LIQUIDCLIENT)/css   $(SITE)/
	cp -r $(LIQUIDCLIENT)/js    $(SITE)/

indexhtml: $(INDEX)
	pandoc --from=markdown+lhs --to=html5 --template=$(INDEX) $(PREAMBLE) -o $(SITE)/index.html

$(INDEX):
	$(INDEXER) src/ $(METATEMPLATE) $(INDEXTEMPLATE) $(PAGETEMPLATE) $(INDEX) $(LINKS)

src/%.html: src/%.lhs
	PANDOC_TARGET=$@ PANDOC_CODETEMPLATE=$(LIQUIDCLIENT)/templates/code.template $(PANDOCHTML) --template=$(PAGETEMPLATE) $(PREAMBLE) $? templates/bib.lhs -o $@

clean:
	rm -rf $(DIST)/* && rm -rf $(SITE)/* && rm -rf src/*.tex && rm -rf src/.liquid && rm -rf src/*.html

rsync:
	$(RSYNC) _site/ $(remoteuser) $(remotehost) $(remotedir)
