#![allow(dead_code, unused_mut)]
use {
    std::sync::Arc,
    tokio::{
        sync::mpsc::{self, Receiver, Sender},
        time::Instant,
    }, // tokio_stream::{self as stream, StreamExt},
};

const LIMIT: usize = 1_000_000;
const BUFF_SIZE: usize = 10;

#[tokio::main]
async fn main() -> Result<(), ()> {
    let now = Instant::now();
    let _ = main2().await;
    let finished = Instant::now();
    println!("{:.3}", ((finished - now).as_millis() as f64) / 1000.0_f64);
    Ok(())
}

fn main1() -> Result<(), ()> {
    let dict = build_dict();
    let values = build_sequence();
    println!("Hello, world: {:?}!", &dict[6400..6580]);
    println!("Hello, world: {:?}!", &values[6400..6580]);
    let x: isize = values
        .iter()
        .map(|x| {
            if let Some((i, _)) = dict.iter().enumerate().find(|entry| entry.1 == x) {
                i as isize
            } else {
                -1_isize
            }
        })
        .sum();
    println!("{x}");
    Ok(())
}

async fn main2() -> Result<(), ()> {
    // let pool = ThreadPool::new().expect("failed");
    let future = helloworld();
    let dict = Arc::new(Box::new(build_dict()));
    let values = Arc::new(Box::new(build_sequence()));

    // channels
    // let (mut data_in, mut data_out) = mpsc::channel::<usize>(BUFF_SIZE);

    let (mut result_in, mut _result_out) = mpsc::channel::<usize>(BUFF_SIZE);

    // receiver
    let dict1 = dict.clone();
    let result_in1 = result_in.clone();
    let values1 = values.clone();
    let t1 = tokio::spawn(async move {
        let _ = evaluator(1, values1, result_in1, dict1).await;
    });
    let dict2 = dict.clone();
    let result_in2 = result_in.clone();
    let values2 = values.clone();
    // let data_out2 = data_out.clone();
    let t2 = tokio::spawn(async move {
        let _ = evaluator(2, values2, result_in2, dict2).await;
    });

    // sender
    // tokio::spawn(async move {
    //     for (_i, d) in values.iter().enumerate() {
    //         data_in.send(*d).await.unwrap();
    //     }
    // });
    // let _ = main1();
    // let x: isize = values
    //     .iter()
    //     .map(|x| {
    //         if let Some((i, _)) = dict.iter().enumerate().find(|entry| entry.1 == x) {
    //             i as isize
    //         } else {
    //             -1_isize
    //         }
    //     })
    //     .sum();
    // println!("{x}");
    future.await;
    let _ = t1.await.unwrap();
    let _ = t2.await.unwrap();
    Ok(())
}

async fn evaluator(
    nth: usize,
    input: Arc<Box<Vec<usize>>>,
    _output: Sender<usize>,
    dict: Arc<Box<Vec<usize>>>,
) -> Result<(), ()> {
    let mut i = nth;
    while i < input.len() {
        let val = input[i];
        let r = if let Some((i, _)) = dict.iter().enumerate().find(|entry| *(entry.1) == val) {
            i as isize
        } else {
            -1_isize
        };
        println!("{r}");
        i += 2;
    }
    return Ok(());
}

async fn helloworld() {
    println!("hello world!");
}

fn build_sequence() -> Vec<usize> {
    let mut vec = vec![0; LIMIT];
    for (i, p) in vec.iter_mut().enumerate() {
        *p = (usize::next_power_of_two(i)) % ((usize::count_ones(i) + 3) as usize)
            * ((i * i) % (usize::count_zeros(i) as usize / 2));
    }
    vec
}

fn build_dict() -> Vec<usize> {
    let mut vec = vec![0; LIMIT / 10];
    let mut pre = 0;
    for (i, p) in vec.iter_mut().enumerate() {
        *p = (usize::next_power_of_two(i)) % ((usize::count_ones(i + 3) + 1) as usize)
            * ((i * i) % (usize::count_zeros(i) as usize));
        if pre == 0 {
            *p = i;
        } else {
            *p = (*p + pre) % 256;
        }
        pre = *p;
    }
    vec
}
