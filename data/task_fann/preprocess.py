with open('./data.bin', 'wb') as f:
    f.write((12).to_bytes(8, 'little'))
