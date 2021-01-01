FROM python:3.7
# Intended to be built from the root of the cryptol git repository

COPY deps/argo argo
RUN pip3 install -r argo/python/requirements.txt
RUN pip3 install -e argo/python
COPY cryptol-remote-api/test-scripts/test-cryptol-remote-api.py /entrypoint.py
ENTRYPOINT ["python3", "/entrypoint.py"]
