FROM python:3.12
# Intended to be built from the root of the cryptol git repository

COPY cryptol-remote-api/python python
RUN pip3 install 'poetry==1.4.2'
RUN cd python && poetry install
COPY cryptol-remote-api/test-cryptol-remote-api.py /python/entrypoint.py
WORKDIR /python
ENTRYPOINT ["poetry", "run", "python","entrypoint.py"]
