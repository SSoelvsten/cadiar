# Include official Isabelle Docker image
FROM makarius/isabelle:Isabelle2021

# Download AFP and setup as Isabelle component
RUN curl https://www.isa-afp.org/release/afp-current.tar.gz -o afp.tar.gz ; \
  mkdir -p afp ; \
  tar -xf afp.tar.gz -C afp --strip-components=1 ; \
  echo "$(pwd)/afp/thys" >> Isabelle/ROOTS ; \
  rm afp.tar.gz

# Build session images
RUN ./Isabelle/bin/isabelle build -o system_heaps -b ROBDD