use tutor_ml_modules::*;

use std::fs::File;
use std::io::Read;

fn main() -> anyhow::Result<()> {
    let name = std::env::args()
        .nth(1)
        .ok_or_else(|| anyhow::anyhow!("no arguments given"))?;
    let mut file = File::open(name)?;
    let mut s = String::new();
    file.read_to_string(&mut s)?;

    let m = parse_string(&s)?;
    let (exsig, e) = elaborate(&mut Default::default(), m)?;

    println!("signature: {}", il::tycon::DisplayTableWrapper(exsig));
    println!("term: {}", e);
    Ok(())
}
