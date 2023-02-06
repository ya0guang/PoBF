#![allow(unused_imports)]

use std::io::{BufRead, BufReader, BufWriter, Error, ErrorKind, Read, Result, Write};
use std::net::TcpStream;
use std::sync::{mpsc, Arc, Mutex};
use std::thread;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

cfg_if::cfg_if! {
  if #[cfg(feature = "task_tvm")] {
      use evaluation_tvm::private_computation;
  } else if #[cfg(feature = "task_fann")] {
      use fann::private_computation;
  } else if #[cfg(feature = "task_fasta")] {
      use fasta::private_computation;
  } else if #[cfg(feature = "task_polybench")] {
      use polybench::private_computation;
  } else if #[cfg(feature = "task_sample")] {
      use sample_add::private_computation;
  }
}

const ENCLAVE_THREAD_STACK_SIZE: usize = 0x8000000;

pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Job>>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
        assert!(size > 0);
        let (sender, receiver) = mpsc::channel();

        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }

    pub fn execute<F>(&self, f: F) -> Result<()>
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);

        self.sender
            .as_ref()
            .unwrap()
            .send(job)
            .map_err(|_| Error::from(ErrorKind::Other))
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        drop(self.sender.take());

        for worker in &mut self.workers {
            println!("Shutting down worker {}", worker.id);

            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Worker {
        let builder = thread::Builder::new()
            .name(format!("worker-{}", id))
            .stack_size(ENCLAVE_THREAD_STACK_SIZE);

        let thread = builder
            .spawn(move || loop {
                let message = receiver.lock().unwrap().recv();

                match message {
                    Ok(job) => {
                        println!("Worker {id} got a job; executing.");

                        job();
                    }
                    Err(_) => {
                        println!("Worker {id} disconnected; shutting down.");
                        break;
                    }
                }
            })
            .unwrap();

        Worker {
            id,
            thread: Some(thread),
        }
    }
}

pub fn handle_client(stream: TcpStream) -> Result<()> {
    #[cfg(feature = "occlum")]
    dcap::dcap_demo();

    let socket_clone = stream.try_clone().unwrap();
    let mut reader = BufReader::new(stream);
    let mut writer = BufWriter::new(socket_clone);

    let mut length_str = String::with_capacity(512);
    reader.read_line(&mut length_str)?;
    let data_len = length_str[..length_str.len() - 1].parse::<usize>().unwrap();
    println!("Data length = {}", data_len);
    let mut input = vec![0u8; data_len];
    reader.read_exact(&mut input)?;
    println!("Read data.");

    let output = perform_task(input);
    let mut vec = vec![0u8; 10000];
    reader.read(&mut vec)?;
    writer.write(output.len().to_string().as_bytes())?;
    writer.write(b"\n")?;
    writer.flush()?;
    writer.write(&output)?;
    writer.write(b"\n")?;
    writer.flush()?;
    println!("Sent data. Length = {}", output.len());
    println!("Finished!");

    Ok(())
}

fn perform_task(input: Vec<u8>) -> Vec<u8> {
    let now = Instant::now();
    #[cfg(feature = "task_polybench")]
    {
        let res = private_computation(input, &|| {
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos() as u64
        });
        println!("{}", String::from_utf8(res.clone()).unwrap());
        let elapsed = now.elapsed();
        println!("Elapsed: {:.2?}", elapsed);
        res
    }

    #[cfg(not(feature = "task_polybench"))]
    {
        let res = private_computation(input);
        let elapsed = now.elapsed();
        println!("Elapsed: {:.2?}", elapsed);

        res
    }
}
