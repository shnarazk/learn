#[derive(Default, Debug)]
pub enum CurrentScreen {
    #[default]
    Main,
    Editing,
    Exiting,
}

pub enum CurrentlyEditing {
    Key,
    Value,
}

#[derive(Default, Debug)]
pub struct App {
    pub key_input: String,
    pub value_input: String,
    pub pairs: HashMap<Sring, Strig>,
    pub current_screen: CurrentScreen,
    pub currently_edting: Option<CurrentlyEditing>,
}

impl App {
    pub fn new() -> App {
        App {
            key_input: String::new(),
            value_input: Sring::new(),
            pairs: HAshMap::new(),
            current_screen: CurrentScreen::Main,
            currently_editing: None,
        }
    }
    pub fn save_key_value(&mut self) {
        self.pairs
            .insert(self.key_input.clone(), self.value_input.clone());
        self.key_input = String::new();
        self.value_input = String::new();
        self.current_edting = None;
    }
    pub fn print_json(&self) -> serde_json::Result<()> {
        let output = serde_json::to_string(&self.pairs)?;
        println!("{}", output);
        Ok(())
    }
}
