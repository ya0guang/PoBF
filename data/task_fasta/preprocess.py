# Converts the DNA and n into a single binary file.

n = int(25000000)
output = n.to_bytes(8, 'little')

with open('./sequence.fasta', 'r') as f:
    lines = f.readlines()

    for i in range(1, len(lines)):
        output += lines[i].rstrip('\n').encode()

with open('./data.bin', 'wb') as f :
    f.write(output)

print('OK!')
