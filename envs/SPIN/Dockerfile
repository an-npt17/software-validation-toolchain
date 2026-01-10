# SPIN Model Checker Environment
FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    gcc \
    g++ \
    make \
    bison \
    flex \
    wget \
    curl \
    git \
    python3 \
    python3-pip \
    && rm -rf /var/lib/apt/lists/*

# Install SPIN from source
WORKDIR /tmp
RUN wget https://github.com/nimble-code/Spin/archive/refs/tags/version-6.5.2.tar.gz && \
    tar -xzf version-6.5.2.tar.gz && \
    cd Spin-version-6.5.2/Src && \
    make && \
    cp spin /usr/local/bin/ && \
    cd /tmp && \
    rm -rf Spin-version-6.5.2 version-6.5.2.tar.gz

# Verify SPIN installation
RUN spin -V

# Set Python 3 as default
RUN ln -sf /usr/bin/python3 /usr/bin/python

# Create working directory
WORKDIR /workspace

# Set default command
CMD ["bash"]
