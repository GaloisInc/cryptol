import sys
import argo_client.connection as argo
import cryptol

connType = sys.argv[1]
host = sys.argv[2]
port = int(sys.argv[3])

if connType == 'socket':
    c = cryptol.connect(argo.RemoteSocketProcess(host, port=port, ipv6=False))
elif connType == 'http':
    c = cryptol.connect(url="http://%s:%d/" % (host,port))
else:
    raise Exception('specify socket or http for connection type')

c.load_module('Cryptol')
assert c.evaluate_expression("1+1").result() == 2
