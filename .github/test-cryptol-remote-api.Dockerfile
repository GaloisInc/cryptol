FROM python:3.7

COPY deps/argo argo
RUN pip3 install -r argo/python/requirements.txt
RUN pip3 install -e argo/python
COPY .github/test-cryptol-remote-api.py /entrypoint.py
ENTRYPOINT ["python3", "/entrypoint.py"]
