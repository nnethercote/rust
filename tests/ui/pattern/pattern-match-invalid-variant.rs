//! Tests invalid enum variant in a match expression.

enum Color {
    Rgb(isize, isize, isize),
    Rgba(isize, isize, isize, isize),
}

fn main() {
    let red: Color = Color::Rgb(255, 0, 0);
    match red {
        Color::Rgb(r, g, b) => {
            println!("rgb");
        }
        Color::Hsl(h, s, l) => {
            //~^ ERROR no variant
            println!("hsl");
        }
    }
}
