FROM makarius/isabelle:Isabelle2021

RUN curl https://www.isa-afp.org/release/afp-current.tar.gz -o afp.tar.gz ; \
  cd Isabelle/src/ ; \
  mkdir -p afp ; \
  tar -xf ../../afp.tar.gz -C afp --strip-components=1 ; \
  cd .. ; \
  echo "src/afp/thys" >> ROOTS ; \
  cd .. ; \
  rm afp.tar.gz

RUN ./Isabelle/bin/isabelle build -o system_heaps -b ROBDD

COPY core/ROOT core/*.thy ./