use lotto::*;

fn main() {

    let mut game = Lotto::new(49, 6, 4);
    game.random_collect_tickets();

    /*
    let mut args = env::args();
    args.next();
    let perms = match args.next() {
        Some(arg) => arg.parse::<u16>().unwrap(),
        None => 0u16,
    };

    if perms > 0 {
        game.collect_tickets(&random_permutations(49, perms));
    } else {
        game.collect_tickets(&[]);
    }
    */

    let matches = game.tickets_combo_matches(16);
    println!(
        "ticket: {}, pick-combo: {}",
        game.tickets.len(),
        game.combos.len()
    );
    println!("combo matches: {:?}", matches)
}
