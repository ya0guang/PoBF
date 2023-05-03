use std::{
    fmt::Debug,
    io::{Error, ErrorKind, Result},
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc, Mutex,
    },
    thread::{Builder, JoinHandle},
};

use log::info;

pub type Job = Box<dyn FnOnce() + Send + Sync + 'static>;

pub const TCS_NUM: usize = 10;
pub const THREAD_STACK_SIZE: usize = 0x8000000;

pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<Sender<Job>>,
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        drop(self.sender.take());

        self.workers.iter_mut().for_each(|worker| {
            info!("[+] Shutting down worker {worker:?}");

            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        });
    }
}

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
        assert!(size > 0);
        let (sender, receiver) = channel();

        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        (0..size).for_each(|id| {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        });

        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }

    pub fn execute<F>(&self, f: F) -> Result<()>
    where
        F: FnOnce() + Send + Sync + 'static,
    {
        let job = Box::new(f);

        self.sender
            .as_ref()
            .unwrap()
            .send(job)
            .or_else(|_| Err(Error::from(ErrorKind::Other)))
    }
}

pub struct Worker {
    id: usize,
    thread: Option<JoinHandle<()>>,
}

impl Worker {
    pub fn new(id: usize, receiver: Arc<Mutex<Receiver<Job>>>) -> Self {
        let builder = Builder::new()
            .name(format!("worker-{id}"))
            .stack_size(THREAD_STACK_SIZE);

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

impl Debug for Worker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)
    }
}
