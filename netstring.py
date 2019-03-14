
def encode(string):
    bytestring = string.encode()
    return str(len(bytestring)).encode() + b':' + bytestring + b','

def decode(netstring):
    i = 0
    length_bytes = bytearray(b'')
    while chr(netstring[i]).isdigit():
        length_bytes.append(netstring[i])
        i += 1
    if chr(netstring[i]).encode() != b':':
        raise ValueError("Malformed netstring, missing :")
    length = int(length_bytes.decode())
    i += 1
    out = bytearray(b'')
    for j in range(0, length):
        out.append(netstring[i])
        i += 1
    if chr(netstring[i]).encode() != b',':
        raise ValueError("Malformed netstring, missing ,")
    i += 1
    return (out.decode(), netstring[i:])
