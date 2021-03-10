FROM python:3.9
# Intended to be built from the root of the cryptol git repository

COPY cryptol-remote-api/python python
RUN pip3 install -r python/requirements.txt
RUN pip3 install -e python
COPY cryptol-remote-api/test-cryptol-remote-api.py /entrypoint.py
ENTRYPOINT ["python3", "/entrypoint.py"]
