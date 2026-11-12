FROM ubuntu:24.04@sha256:534baea6a22c03a63003dbc8dbe78fe34bc0d7e595d9a9dc9834884ff530eb55
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl git zstd python3 && rm -rf /var/lib/apt/lists/*
RUN curl --fail --location --connect-timeout 20 --max-time 240 --retry 2 https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst -o /tmp/lean.tar.zst \
    && echo "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  /tmp/lean.tar.zst" | sha256sum -c - \
    && mkdir /opt/lean && tar --zstd -xf /tmp/lean.tar.zst -C /opt/lean --strip-components=1 && rm /tmp/lean.tar.zst
ENV PATH="/opt/lean/bin:$PATH"
WORKDIR /work
COPY lean-toolchain lakefile.toml lake-manifest.json ./
RUN lake exe cache get Mathlib.Analysis.Asymptotics.Defs Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Tactic \
    && rm -rf /root/.cache/mathlib \
    && chmod -R a+rX /work /opt/lean && chown -R 1000:1000 /work
ENV HOME=/tmp
USER 1000:1000

