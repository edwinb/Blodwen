FROM base/archlinux
RUN pacman -Sy --noconfirm idris make clang chicken racket
ENV IDRIS_CC=clang
ADD . /blodwen
RUN cd /blodwen && make blodwen PREFIX=/opt/blodwen && make install PREFIX=/opt/blodwen
FROM debian
RUN apt-get update && apt-get install libgmp10 && apt-get clean autoclean && apt-get autoremove --yes && rm -rf /var/lib/{apt,dpkg,cache,log}/
COPY --from=0 /opt/blodwen /opt/blodwen
CMD ["/opt/blodwen/bin/blodwen"]