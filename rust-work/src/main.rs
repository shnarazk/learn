#[tokio::main]
async fn main() -> Result<(), ()> {
    let dict = build_dict();
    println!("Hello, world: {:?}!", &dict[6400..6580]);
    let v = build_sequence();
    println!("Hello, world: {:?}!", &v[6400..6580]);
    Ok(())
}

fn build_sequence() -> Vec<usize> {
    let mut vec = vec![0; 100000];
    for (i, p) in vec.iter_mut().enumerate() {
        *p = (usize::next_power_of_two(i)) % ((usize::count_ones(i) + 3) as usize)
            * ((i * i) % (usize::count_zeros(i) as usize / 2));
    }
    vec
}

fn build_dict() -> Vec<usize> {
    let mut vec = vec![0; 100000];
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
