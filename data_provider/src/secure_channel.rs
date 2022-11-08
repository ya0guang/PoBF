use std::io::*;
use std::net::TcpStream;

use log::error;

use crate::dh::KeyPair;

/// Secure Tcp Stream used to transmit data between the data provider and the enclave.
/// The key is computed by ECDH algorithm. The channel serves as a quasi-TLS stream.
#[derive(Debug)]
pub struct SecureChannel {
    reader: BufReader<TcpStream>,
    writer: BufWriter<TcpStream>,
    key_pair: Option<KeyPair>,
}

impl SecureChannel {
    fn check_key(&self) -> Result<()> {
        if self.key_pair.is_none() {
            error!("[-] The stream has no key!");
            Err(Error::from(ErrorKind::NotConnected))
        } else {
            Ok(())
        }
    }

    pub fn new(socket: TcpStream) -> Self {
        let socket_clone = socket.try_clone().unwrap();

        Self {
            reader: BufReader::new(socket),
            writer: BufWriter::new(socket_clone),
            key_pair: None,
        }
    }

    pub fn set_key(&mut self, key_pair: KeyPair) {
        self.key_pair = Some(key_pair);
    }

    pub fn read_str(&mut self, buf: &mut String) -> Result<()> {
        self.check_key()?;

        self.reader.read_line(buf)?;
        // Decrypt the message.
        let decrypted = self
            .key_pair
            .as_ref()
            .unwrap()
            .decrypt_with_smk(&buf.as_bytes().to_vec())
            .or_else(|e| {
                error!("[-] Decryption failed due to {:?}.", e);
                Err(Error::from(ErrorKind::InvalidData))
            })?;

        // Copy back.
        *buf = String::from_utf8(decrypted).or_else(|e| {
            error!("[-] String convertion failed due to {:?}.", e);
            Err(Error::from(ErrorKind::InvalidData))
        })?;

        Ok(())
    }

    pub fn write_str(&mut self, buf: &String) -> Result<()> {
        self.check_key()?;

        let encrypted = self
            .key_pair
            .as_ref()
            .unwrap()
            .encrypt_with_smk(&buf.as_bytes().to_vec())
            .or_else(|e| {
                error!("[-] Encryption failed due to {:?}.", e);
                Err(Error::from(ErrorKind::InvalidData))
            })?;

        self.writer.write(&encrypted)?;

        Ok(())
    }

    pub fn read_bytes(&mut self, buf: &mut [u8]) -> Result<()> {
        self.check_key()?;

        self.reader.read_exact(buf)?;

        // Decrypt the byte array.
        let decrypted = self
            .key_pair
            .as_ref()
            .unwrap()
            .decrypt_with_smk(&buf.to_vec())
            .or_else(|e| {
                error!("[-] Decryption failed due to {:?}.", e);
                Err(Error::from(ErrorKind::InvalidData))
            })?;

        buf.copy_from_slice(&decrypted);

        Ok(())
    }

    pub fn write_bytes(&mut self, buf: &[u8]) -> Result<()> {
        self.check_key()?;

        let encrypted = self
            .key_pair
            .as_ref()
            .unwrap()
            .encrypt_with_smk(&buf.to_vec())
            .or_else(|e| {
                error!("[-] Encryption failed due to {:?}.", e);
                Err(Error::from(ErrorKind::InvalidData))
            })?;

        self.writer.write(&encrypted)?;

        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.writer.flush()
    }
}
